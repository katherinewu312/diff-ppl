(** Path integration: turn a path's samples and condition into

      P(path) = ∫ ∏ₖ densityₖ(sampleₖ) · 1[condition] d(samples)

    Draws with finite outcomes are summed out first. The remaining samples
    are eliminated from the last drawn to the first (later draws may depend
    on earlier ones, never the reverse). A sample whose constraints are all
    linear bounds, and which the accumulated factor does not mention, is
    eliminated in closed form with its CDF; otherwise it becomes an
    [Expr.Integral] node, evaluated numerically once parameters are fixed. *)
module S = Symbolic
open Expr

exception Unsupported of string

let constrains id term = List.mem id (S.samples term)

let rec number = function
  | S.Number n -> Const n
  | S.Parameter p -> Param p
  | S.Sample k -> Var k
  | S.Binary (S.Add,a,b) -> add (number a) (number b)
  | S.Binary (S.Sub,a,b) -> sub (number a) (number b)
  | S.Binary (S.Mul,a,b) -> mul (number a) (number b)
  | S.Binary (S.Div,a,b) -> div (number a) (number b)
  | t -> raise (Unsupported ("non-numeric term " ^ S.to_string t))

let rec condition = function
  | S.Binary (S.Lt,a,b) -> Compare (Lt, number a, number b)
  | S.Binary (S.Le,a,b) -> Compare (Le, number a, number b)
  | S.Binary (S.Eq,a,b) -> Compare (Eq, number a, number b)
  | S.Not t -> Not (condition t)
  | S.Parameter p -> Bool_param p
  | t -> raise (Unsupported ("condition " ^ S.to_string t))

(** [linear x t = Some (a, r)] when [t = a*x + r] with [a] a number and
    [r] free of [x]. *)
let rec linear x t =
  if not (constrains x t) then Some (0., t) else
  let scale k (a,r) = k *. a, S.binary S.Mul (S.Number k) r in
  match t with
  | S.Sample k when k = x -> Some (1., S.Number 0.)
  | S.Binary ((S.Add | S.Sub) as op,p,q) ->
      (match linear x p, linear x q with
       | Some (a,r), Some (b,s) ->
           Some ((if op = S.Add then a +. b else a -. b), S.binary op r s)
       | _ -> None)
  | S.Binary (S.Mul,S.Number k,q) -> Option.map (scale k) (linear x q)
  | S.Binary (S.Mul,p,S.Number k) -> Option.map (scale k) (linear x p)
  | S.Binary (S.Div,p,S.Number k) when k <> 0. -> Option.map (scale (1. /. k)) (linear x p)
  | _ -> None

type bound = Upper of Expr.t * bool | Lower of Expr.t * bool  (** threshold, strict *)

(** How a constraint restricts sample [x]. *)
type restriction =
  | Bounds of bound list
  | Almost_surely  (** [x <> c] for continuous [x] *)
  | Other

let restriction ~continuous x c =
  let relation = match c with
    | S.Binary ((S.Lt | S.Le | S.Eq) as op,a,b) -> Some (op,a,b)
    | S.Not (S.Binary (S.Lt,a,b)) -> Some (S.Le,b,a)
    | S.Not (S.Binary (S.Le,a,b)) -> Some (S.Lt,b,a)
    | _ -> None
  in
  match relation with
  | Some (op,a,b) ->
      (match linear x (S.binary S.Sub a b) with
       | Some (k,r) when k <> 0. ->
           (* k*x + r op 0 *)
           let t = div (neg (number r)) (Const k) in
           let strict = op = S.Lt in
           if op = S.Eq then Bounds [Upper (t,false); Lower (t,false)]
           else if k > 0. then Bounds [Upper (t,strict)]
           else Bounds [Lower (t,strict)]
       | _ -> Other)
  | None ->
      (match c with
       | S.Not (S.Binary (S.Eq,a,b)) when continuous
           && Option.is_some (linear x (S.binary S.Sub a b)) -> Almost_surely
       | _ -> Other)

(** [P(X <= x)] for [X ~ d(params)]: a closed form where elementary (in
    GSL's parameterisations), otherwise an [Expr.Cdf] node. *)
let cdf (d : Distribution.t) params x =
  match d, params with
  | Uniform, [a;b] when a = b -> indicator (Compare (Le, a, x))
  | Uniform, [a;b] -> clamp (div (sub x a) (sub b a)) zero one
  | Gaussian, [m;s] ->
      mul (Const 0.5) (add one (erf (div (sub x m) (mul s (Const (sqrt 2.))))))
  | Exponential, [rate] -> sub one (exp (neg (mul rate (max x zero))))
  | _ -> Cdf (d, params, x)

(** [P(X < x)]; differs from [cdf] only for integer-valued distributions. *)
let cdf_below d params x =
  if Distribution.integer_valued d then cdf d params (sub (ceil x) one) else cdf d params x

let fold_or f = function [] -> None | e :: es -> Some (List.fold_left f e es)

(** Probability that [x ~ d(params)] satisfies all [bounds]. For continuous
    [x], [x < a && x < b] is [x < min(a,b)]. *)
let interval d params bounds =
  let uppers = List.filter_map (function Upper (t,s) -> Some (t,s) | _ -> None) bounds in
  let lowers = List.filter_map (function Lower (t,s) -> Some (t,s) | _ -> None) bounds in
  let below_upper, below_lower =
    if Distribution.integer_valued d then
      (* nested events: the intersection has the smallest probability *)
      fold_or min (List.map (fun (t,strict) ->
        if strict then cdf_below d params t else cdf d params t) uppers),
      fold_or max (List.map (fun (t,strict) ->
        if strict then cdf d params t else cdf_below d params t) lowers)
    else
      Option.map (cdf d params) (fold_or min (List.map fst uppers)),
      Option.map (cdf d params) (fold_or max (List.map fst lowers))
  in
  match below_upper, below_lower with
  | None, None -> one
  | Some u, None -> u
  | None, Some l -> sub one l
  | Some u, Some l -> max zero (sub u l)

let indicators factor constraints =
  List.fold_left (fun e c -> mul e (indicator (condition c))) factor constraints

(** Sum a finite draw out of the constraints that mention it. *)
let sum_outcomes (sample : Path.sample) outcomes constraints =
  let mine, others = List.partition (constrains sample.id) constraints in
  if List.exists (fun c -> S.samples c <> [sample.id]) mine then
    raise (Unsupported (Printf.sprintf "sample#%d is constrained jointly with other samples" sample.id));
  let weight = List.fold_left (fun acc (value,w) ->
    let satisfied = List.for_all (fun c ->
      match S.substitute sample.id value c with
      | S.Boolean b -> b
      | t -> raise (Unsupported ("condition " ^ S.to_string t))) mine in
    if satisfied then add acc (number w) else acc) zero outcomes in
  others, weight

let rec eliminate samples constraints factor =
  match samples with
  | [] -> indicators factor constraints
  | (x : Path.sample) :: rest ->
      let d = x.distribution and params = List.map number x.parameters in
      let continuous = not (Distribution.integer_valued d) in
      let mine, others = List.partition (constrains x.id) constraints in
      let restrictions = List.map (fun c -> c, restriction ~continuous x.id c) mine in
      let bounds = List.concat_map (function _, Bounds b -> b | _ -> []) restrictions in
      let other = List.filter_map (function c, Other -> Some c | _ -> None) restrictions in
      if other = [] && not (Expr.mentions x.id factor) then
        eliminate rest others (mul factor (interval d params bounds))
      else
        let i =
          if continuous then
            let uppers = List.filter_map (function Upper (t,_) -> Some t | _ -> None) bounds in
            let lowers = List.filter_map (function Lower (t,_) -> Some t | _ -> None) bounds in
            { var=x.id; distribution=d; parameters=params;
              lower=fold_or max lowers; upper=fold_or min uppers;
              body=indicators factor other }
          else
            { var=x.id; distribution=d; parameters=params;
              lower=None; upper=None; body=indicators factor mine }
        in
        eliminate rest others (integral i)

(** Probability of reaching the end of the path, as an expression in the
    remaining symbolic parameters. *)
let probability (s : Path.state) =
  let finite, rest = List.partition_map (fun (x : Path.sample) ->
    match Distribution.outcomes x.distribution x.parameters with
    | Some outcomes -> Left (x, outcomes)
    | None -> Right x) s.samples in
  let constraints, weight = List.fold_left (fun (constraints,weight) (x,outcomes) ->
    let constraints, w = sum_outcomes x outcomes constraints in
    constraints, mul weight w) (s.constraints, one) finite in
  let latest_first = List.sort (fun (a : Path.sample) b -> compare b.id a.id) rest in
  eliminate latest_first constraints weight
