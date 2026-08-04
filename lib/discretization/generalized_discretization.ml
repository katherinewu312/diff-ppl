(* Exact joint-region extension for Slice discretization.

   The legacy analysis attaches scalar cuts to each float and the legacy
   rewriter turns a primitive sample into its one-dimensional cut intervals.
   This pass runs just before that rewriter.  It discovers arithmetic
   predicates whose provenance cannot be represented by a scalar cut, builds
   connected components of primitive samples, computes exact analytic masses
   for the deliberately small geometry language below, and replaces each
   component with one finite region variable.  Expressions not claimed by
   this pass are subsequently handled by the unchanged cut discretizer. *)

open Ast

module IntSet = Set.Make(Int)
module StringMap = Map.Make(String)

let list_find_index pred xs =
  let rec loop i = function
    | [] -> None
    | x :: rest -> if pred x then Some i else loop (i + 1) rest
  in
  loop 0 xs

type sample_info = {
  id : sample_id;
  lo : float option;
  hi : float option;
  guarded : bool;
}

type predicate = {
  op : cmp_op;
  left : sym_expr;
  right : sym_expr;
  deps : IntSet.t;
}

type analysis = {
  samples : sample_info list;
  predicates : predicate list;
  seeds : predicate list;
}

let unsupported fmt =
  Printf.ksprintf
    (fun detail -> failwith ("Generalized discretization unsupported: " ^ detail))
    fmt

let rec deps = function
  | SConst _ | SParam _ -> IntSet.empty
  | SSample id -> IntSet.singleton id
  | SNeg x -> deps x
  | SAdd (a, b) | SMul (a, b) | SDiv (a, b) -> IntSet.union (deps a) (deps b)

let rec string_of_sym_expr = function
  | SConst f -> Printf.sprintf "%g" f
  | SParam name -> name
  | SSample id -> Printf.sprintf "u%d" id
  | SNeg x -> "(-" ^ string_of_sym_expr x ^ ")"
  | SAdd (a,b) -> "(" ^ string_of_sym_expr a ^ "+" ^ string_of_sym_expr b ^ ")"
  | SMul (a,b) -> "(" ^ string_of_sym_expr a ^ "*" ^ string_of_sym_expr b ^ ")"
  | SDiv (a,b) -> "(" ^ string_of_sym_expr a ^ "/" ^ string_of_sym_expr b ^ ")"

let rec contains_parameter = function
  | SParam _ -> true
  | SConst _ | SSample _ -> false
  | SNeg x -> contains_parameter x
  | SAdd (a,b) | SMul (a,b) | SDiv (a,b) ->
      contains_parameter a || contains_parameter b

let commutative ctor a b =
  if compare_sym_expr a b <= 0 then ctor a b else ctor b a

let sadd a b = commutative (fun x y -> SAdd (x, y)) a b
let smul a b = commutative (fun x y -> SMul (x, y)) a b

let is_scalar_cut = function
  | SSample _, rhs | rhs, SSample _ -> IntSet.is_empty (deps rhs)
  | _ -> false

let const = function ExprNode (Const f) -> Some f | _ -> None

let analyze (root : expr) : analysis =
  let next_id = ref 0 in
  let samples = ref [] in
  let predicates = ref [] in
  let seeds = ref [] in
  let rec walk guarded env (ExprNode node) =
    let binary ctor a b =
      let sa = walk guarded env a in
      let sb = walk guarded env b in
      match sa, sb with Some x, Some y -> Some (ctor x y) | _ -> None
    in
    match node with
    | Const f -> Some (SConst f)
    | Var x ->
        (match StringMap.find_opt x env with
         | Some provenance -> provenance
         | None -> Some (SParam x))
    | Add (a, b) -> binary sadd a b
    | Sub (a, b) -> binary (fun x y -> sadd x (SNeg y)) a b
    | Mul (a, b) -> binary smul a b
    | Div (a, b) -> binary (fun x y -> SDiv (x, y)) a b
    | Sample dist ->
        let walk_arg = walk guarded env in
        (match dist with
         | Distr1 (_, a) -> ignore (walk_arg a)
         | Distr2 (_, a, b) -> ignore (walk_arg a); ignore (walk_arg b));
        let id = !next_id in
        incr next_id;
        let lo, hi =
          match dist with
          | Distr2 (DUniform, a, b) -> const a, const b
          | _ -> None, None
        in
        samples := { id; lo; hi; guarded } :: !samples;
        Some (SSample id)
    | Let (x, a, b) ->
        let sa = walk guarded env a in
        walk guarded (StringMap.add x sa env) b
    | Cmp (op, a, b, _) ->
        let sa = walk guarded env a in
        let sb = walk guarded env b in
        (match sa, sb with
         | Some left, Some right ->
             let p = { op; left; right; deps = IntSet.union (deps left) (deps right) } in
             if not (IntSet.is_empty p.deps) then begin
               predicates := p :: !predicates;
               if not (is_scalar_cut (left, right)) then seeds := p :: !seeds
             end
         | _ -> ());
        None
    | If (c, t, f) ->
        ignore (walk guarded env c);
        ignore (walk true env t);
        ignore (walk true env f);
        None
    | Pair (a, b) | And (a, b) | Or (a, b) | FuncApp (a, b)
    | FinEq (a, b, _) | FinCmp (_, a, b, _, _)
    | Cons (a, b) | Assign (a, b) | Seq (a, b) ->
        ignore (walk guarded env a); ignore (walk guarded env b); None
    | Not a | First a | Second a | Observe a | Ref a | Deref a
    | Reset a -> ignore (walk guarded env a); None
    | Fun (_, a) | Fix (_, _, a) | Shift (_, a) ->
        ignore (walk true env a); None
    | MatchList (a, b, _, _, c) ->
        ignore (walk guarded env a); ignore (walk true env b);
        ignore (walk true env c); None
    | DiscreteCase cases ->
        List.iter (fun (a, p) -> ignore (walk true env a); ignore (walk guarded env p)) cases;
        None
    | SpecialFunc (_, args) -> List.iter (fun a -> ignore (walk guarded env a)) args; None
    | Cdf (d, a) ->
        (match d with Distr1 (_, x) -> ignore (walk guarded env x)
         | Distr2 (_, x, y) -> ignore (walk guarded env x); ignore (walk guarded env y));
        ignore (walk guarded env a); None
    | CdfJvp (d, ts, x, dx) ->
        (match d with Distr1 (_, a) -> ignore (walk guarded env a)
         | Distr2 (_, a, b) -> ignore (walk guarded env a); ignore (walk guarded env b));
        List.iter (fun a -> ignore (walk guarded env a)) ts;
        ignore (walk guarded env x); ignore (walk guarded env dx); None
    | CdfVjp (d, _, x, _, bar) ->
        (match d with Distr1 (_, a) -> ignore (walk guarded env a)
         | Distr2 (_, a, b) -> ignore (walk guarded env a); ignore (walk guarded env b));
        ignore (walk guarded env x); ignore (walk guarded env bar); None
    | CdfExpr (a, b) -> ignore (walk guarded env a); ignore (walk guarded env b); None
    | BoolConst _ | FinConst _ | Nil | Unit | RuntimeError _ -> None
  in
  ignore (walk false StringMap.empty root);
  { samples = List.rev !samples; predicates = List.rev !predicates;
    seeds = List.rev !seeds }

type uf = (int, int ref) Hashtbl.t

let uf_find table x =
  let rec find x =
    let p = !(Hashtbl.find table x) in
    if p = x then x else let r = find p in Hashtbl.replace table x (ref r); r
  in find x

let uf_union table a b =
  let a = uf_find table a and b = uf_find table b in
  if a <> b then Hashtbl.replace table b (ref a)

let complexity p =
  let rec size = function
    | SConst _ | SParam _ | SSample _ -> 1 | SNeg x -> 1 + size x
    | SAdd (a,b) | SMul (a,b) | SDiv (a,b) -> 1 + size a + size b
  in size p.left + size p.right

let predicate_compare a b =
  let c = compare (complexity b) (complexity a) in
  if c <> 0 then c else
  let c = compare_sym_expr a.left b.left in
  if c <> 0 then c else
  let c = compare_sym_expr a.right b.right in
  if c <> 0 then c else compare a.op b.op

type component = {
  ids : IntSet.t;
  predicates : predicate list;
  var : string;
  regions : (bool list * expr) list;
}

let rec expr_of_parameter = function
  | SConst f -> ExprNode (Const f)
  | SParam name -> ExprNode (Var name)
  | SNeg x -> ExprNode (Sub (ExprNode (Const 0.0), expr_of_parameter x))
  | SAdd (a,b) -> ExprNode (Add (expr_of_parameter a, expr_of_parameter b))
  | SMul (a,b) -> ExprNode (Mul (expr_of_parameter a, expr_of_parameter b))
  | SDiv (a,b) -> ExprNode (Div (expr_of_parameter a, expr_of_parameter b))
  | SSample id -> unsupported "sample u%d occurs in a symbolic parameter expression" id

let symbolic_unit_square_radial_cdf threshold =
  (* Like the scalar [Cdf] node, keep the exact parameterized integral opaque
     in generated Slice.  The callback evaluates the analytic, piecewise
     unit-square formula; no quadrature is involved. *)
  ExprNode
    (SpecialFunc
       ("unit_square_radial_cdf", [expr_of_parameter threshold]))

let linear ids expr =
  let n = List.length ids in
  let zero () = Array.make n 0.0 in
  let add (c1, a1) (c2, a2) =
    (c1 +. c2, Array.init n (fun i -> a1.(i) +. a2.(i)))
  in
  let scale k (c, a) = (k *. c, Array.map (( *. ) k) a) in
  let rec go = function
    | SConst c -> Some (c, zero ())
    | SParam _ -> None
    | SSample id ->
        (match list_find_index ((=) id) ids with
         | None -> None
         | Some i -> let a = zero () in a.(i) <- 1.0; Some (0.0, a))
    | SNeg x -> Option.map (scale (-1.0)) (go x)
    | SAdd (a,b) -> Option.bind (go a) (fun a -> Option.map (add a) (go b))
    | SMul (a,b) ->
        (match go a, go b with
         | Some ((ca, aa) as xa), Some ((cb, ab) as xb) ->
             let za = Array.for_all ((=) 0.0) aa in
             let zb = Array.for_all ((=) 0.0) ab in
             if za then Some (scale ca xb) else if zb then Some (scale cb xa) else None
         | _ -> None)
    | SDiv (a,b) ->
        (match go a, go b with
         | Some xa, Some (cb, ab) when cb <> 0.0 && Array.for_all ((=) 0.0) ab ->
             Some (scale (1.0 /. cb) xa)
         | _ -> None)
  in go expr

let polygon_area poly =
  match poly with
  | [] | [_] | [_;_] -> 0.0
  | _ ->
      let rec sum acc = function
        | (x1,y1) :: ((x2,y2) :: _ as rest) -> sum (acc +. x1*.y2 -. y1*.x2) rest
        | _ -> acc
      in
      let closed = poly @ [List.hd poly] in
      abs_float (sum 0.0 closed) /. 2.0

let clip_polygon (a,b,c) poly =
  let inside (x,y) = a*.x +. b*.y +. c <= 1e-12 in
  let intersection (x1,y1) (x2,y2) =
    let d1 = a*.x1 +. b*.y1 +. c in
    let d2 = a*.x2 +. b*.y2 +. c in
    let t = d1 /. (d1 -. d2) in
    (x1 +. t *. (x2 -. x1), y1 +. t *. (y2 -. y1))
  in
  let rec edges acc = function
    | p :: (q :: _ as rest) ->
        let ip, iq = inside p, inside q in
        let acc = match ip, iq with
          | true, true -> q :: acc
          | true, false -> intersection p q :: acc
          | false, true -> q :: intersection p q :: acc
          | false, false -> acc
        in edges acc rest
    | _ -> List.rev acc
  in
  match poly with [] -> [] | _ -> edges [] (poly @ [List.hd poly])

let square_term = function
  | SMul (SSample a, SSample b) when a = b -> Some a
  | _ -> None

let radial ids p =
  let identify expr = match expr with
    | SAdd (a,b) ->
        Option.bind (square_term a) (fun x ->
          Option.bind (square_term b) (fun y ->
            if IntSet.equal (IntSet.of_list [x;y]) (IntSet.of_list ids)
            then Some () else None))
    | _ -> None
  in
  match identify p.left, p.right with
  | Some (), SConst t -> Some t
  | _ -> None

let radial_symbolic_threshold ids p =
  let identify expr = match expr with
    | SAdd (a,b) ->
        Option.bind (square_term a) (fun x ->
          Option.bind (square_term b) (fun y ->
            if IntSet.equal (IntSet.of_list [x;y]) (IntSet.of_list ids)
            then Some () else None))
    | _ -> None
  in
  let rec parameter_only = function
    | SConst _ | SParam _ -> true
    | SNeg x -> parameter_only x
    | SAdd (a,b) | SMul (a,b) | SDiv (a,b) ->
        parameter_only a && parameter_only b
    | SSample _ -> false
  in
  match identify p.left with
  | Some () when parameter_only p.right -> Some p.right
  | _ -> None

let primitive_circle t x =
  if t <= 0.0 then 0.0 else
  let r = sqrt t in
  let x = max (-.r) (min r x) in
  0.5 *. (x *. sqrt (max 0.0 (t -. x*.x)) +. t *. asin (x /. r))

let circle_rectangle_area t x0 x1 y0 y1 =
  if t <= 0.0 || x1 <= x0 || y1 <= y0 then 0.0 else
  let roots y = if t <= y*.y then 0.0 else sqrt (t -. y*.y) in
  let points =
    [x0; x1; roots y0; roots y1; sqrt t]
    |> List.filter (fun x -> x > x0 && x < x1)
    |> List.sort_uniq compare
  in
  let points = x0 :: points @ [x1] in
  let rec integrate acc = function
    | a :: (b :: _ as rest) ->
        let m = (a +. b) /. 2.0 in
        let h = if m*.m >= t then 0.0 else sqrt (t -. m*.m) in
        let area =
          if h <= y0 then 0.0
          else if h >= y1 then (b -. a) *. (y1 -. y0)
          else primitive_circle t b -. primitive_circle t a -. y0 *. (b -. a)
        in integrate (acc +. area) rest
    | _ -> acc
  in integrate 0.0 points

let eval_sym values =
  let rec go = function
    | SConst f -> f | SSample id -> List.assoc id values | SNeg a -> -. go a
    | SParam name -> unsupported "cannot numerically evaluate symbolic parameter %s" name
    | SAdd (a,b) -> go a +. go b | SMul (a,b) -> go a *. go b
    | SDiv (a,b) -> go a /. go b
  in go

let predicate_truth p values =
  match p.op with Lt -> eval_sym values p.left < eval_sym values p.right
  | Le -> eval_sym values p.left <= eval_sym values p.right

let one_dim_mass id lo hi predicates bits =
  let roots = ref [lo; hi] in
  let add x = if x > lo && x < hi then roots := x :: !roots in
  List.iter (fun p ->
    match linear [id] (SAdd (p.left, SNeg p.right)) with
    | Some (c,a) when a.(0) <> 0.0 -> add (-.c /. a.(0))
    | _ ->
        let square = function
          | SMul (SSample a, SSample b) when a=id && b=id -> true | _ -> false
        in
        (match p.left, p.right with
         | x, SConst t when square x && t >= 0.0 -> add (sqrt t); add (-.sqrt t)
         | _ -> unsupported "one-dimensional predicate has no exact supported integral"))
    predicates;
  let points = List.sort_uniq compare !roots in
  let rec total acc = function
    | a :: (b :: _ as rest) ->
        let values = [id, (a+.b)/.2.0] in
        let ok = List.for_all2 (fun p bit -> predicate_truth p values = bit) predicates bits in
        total (if ok then acc +. b -. a else acc) rest
    | _ -> acc
  in total 0.0 points /. (hi -. lo)

(* Do the 1D/2D integration *)
let component_mass infos predicates bits =
  let ids = List.map (fun s -> s.id) infos in
  match infos with
  | [{id; lo=Some lo; hi=Some hi; _}] -> one_dim_mass id lo hi predicates bits
  | [{lo=Some x0; hi=Some x1; _}; {lo=Some y0; hi=Some y1; _}] ->
      if x1 <= x0 || y1 <= y0 then unsupported "uniform support is empty";
      let radial_present = List.exists (fun p -> Option.is_some (radial ids p)) predicates in
      let area =
        if not radial_present then
          let initial = [x0,y0; x1,y0; x1,y1; x0,y1] in
          List.fold_left2 (fun poly p bit ->
            match linear ids (SAdd (p.left, SNeg p.right)) with
            | Some (c,a) ->
                let sign = if bit then 1.0 else -1.0 in
                clip_polygon (sign*.a.(0), sign*.a.(1), sign*.c) poly
            | None -> unsupported "non-affine predicate in affine component")
            initial predicates bits
          |> polygon_area
        else begin
          if x0 < 0.0 || y0 < 0.0 then
            unsupported "radial backend requires a nonnegative rectangular support";
          let xl = ref x0 and xu = ref x1 and yl = ref y0 and yu = ref y1 in
          let lower = ref 0.0 and upper = ref infinity in
          List.iter2 (fun p bit ->
            match radial ids p with
            | Some t -> if bit then upper := min !upper t else lower := max !lower t
            | None ->
                (match linear ids (SAdd (p.left, SNeg p.right)) with
                 | Some (c,a) ->
                     let nonzero = List.filter (fun i -> a.(i) <> 0.0) [0;1] in
                     (match nonzero with
                      | [i] ->
                          let threshold = -.c /. a.(i) in
                          let less = a.(i) > 0.0 in
                          let want_less = if bit then less else not less in
                          let l,u = if i=0 then xl,xu else yl,yu in
                          if want_less then u := min !u threshold else l := max !l threshold
                      | _ -> unsupported "radial components only support axis affine cuts")
                 | None -> unsupported "unsupported predicate mixed with radial cuts"))
            predicates bits;
          if !xu <= !xl || !yu <= !yl || !upper <= !lower then 0.0 else
          let below t = if classify_float t = FP_infinite then
              (!xu -. !xl) *. (!yu -. !yl)
            else circle_rectangle_area t !xl !xu !yl !yu
          in below !upper -. below !lower
        end
      in area /. ((x1 -. x0) *. (y1 -. y0))
  | _ -> unsupported "exact backend currently supports one or two independent uniforms"

module type REGION_MASS = sig
  val mass :
    sample_info list -> predicate list -> bool list -> (float, string) result
  val is_empty :
    sample_info list -> predicate list -> bool list -> (bool, string) result
end

module Exact_region_mass : REGION_MASS = struct
  let mass infos predicates bits =
    try Ok (component_mass infos predicates bits) with
    | Failure reason -> Error reason
  let is_empty infos predicates bits =
    match mass infos predicates bits with
    | Ok mass -> Ok (mass <= 1e-12)
    | Error reason -> Error reason
end

(* Union-finds seed samples into components. Collect all predicates touching each component. *)
let build_components analysis =
  if analysis.seeds = [] then [] else
  let uf = Hashtbl.create 16 in
  List.iter (fun s -> Hashtbl.add uf s.id (ref s.id)) analysis.samples;
  List.iter (fun p ->
    match IntSet.elements p.deps with
    | [] -> () | x::xs -> List.iter (uf_union uf x) xs) analysis.seeds;
  let seeded = List.fold_left (fun a p -> IntSet.union a p.deps) IntSet.empty analysis.seeds in
  let groups = Hashtbl.create 8 in
  IntSet.iter (fun id ->
    let r = uf_find uf id in
    let old = Option.value (Hashtbl.find_opt groups r) ~default:IntSet.empty in
    Hashtbl.replace groups r (IntSet.add id old)) seeded;
  Hashtbl.to_seq_values groups |> List.of_seq
  |> List.sort (fun a b -> compare (IntSet.min_elt a) (IntSet.min_elt b))
  |> List.mapi (fun index ids ->
      let infos = analysis.samples |> List.filter (fun s -> IntSet.mem s.id ids) in
      List.iter (fun s ->
        if s.guarded then unsupported "component u%d is sampled under control flow" s.id;
        if Option.is_none s.lo || Option.is_none s.hi then
          unsupported "component u%d is not an independent uniform with constant parameters" s.id)
        infos;
      let predicates =
        analysis.predicates
        |> List.filter (fun p -> not (IntSet.is_empty (IntSet.inter p.deps ids)))
        |> List.sort_uniq predicate_compare
      in
      if List.length predicates > 20 then unsupported "component has too many predicates";
      let component_name =
        ids |> IntSet.elements |> List.map (Printf.sprintf "u%d")
        |> String.concat ","
      in
      let exact_mass ps bits =
        match Exact_region_mass.mass infos ps bits with
        | Ok mass -> mass
        | Error reason ->
            let predicate = List.hd (List.rev ps) in
            let op = match predicate.op with Lt -> "<" | Le -> "<=" in
            failwith
              (Printf.sprintf "%s (component {%s}, predicate %s %s %s)"
                 reason component_name (string_of_sym_expr predicate.left) op
                 (string_of_sym_expr predicate.right))
      in
      let symbolic_predicates =
        List.filter
          (fun p -> contains_parameter p.left || contains_parameter p.right)
          predicates
      in
      let regions =
        match symbolic_predicates with
        | [] ->
            (* Refine incrementally. Impossible partial truth patterns
               disappear before the next predicate. *)
            let rec refine prefix active = function
              | [] -> active
              | p :: rest ->
                  let prefix = prefix @ [p] in
                  let active =
                    List.concat_map
                      (fun (bits, _) ->
                         [bits @ [true]; bits @ [false]]
                         |> List.filter_map (fun bits ->
                              let mass = exact_mass prefix bits in
                              if mass > 1e-12 then
                                Some (bits, ExprNode (Const mass))
                              else if mass >= -.1e-10 then None
                              else unsupported
                                "analytic backend produced negative mass %.17g" mass))
                      active
                  in
                  refine prefix active rest
            in
            let regions = refine [] [([], ExprNode (Const 1.0))] predicates in
            let total =
              List.fold_left
                (fun total (_, probability) ->
                   match probability with
                   | ExprNode (Const p) -> total +. p
                   | _ -> failwith "internal numeric region mass")
                0.0 regions
            in
            if abs_float (total -. 1.0) > 1e-9 then
              unsupported "region masses sum to %.17g instead of 1" total;
            regions
        | [p] when predicates = [p] ->
            let unit_support =
              match infos with
              | [{lo=Some 0.0; hi=Some 1.0; _};
                 {lo=Some 0.0; hi=Some 1.0; _}] -> true
              | _ -> false
            in
            if not unit_support then
              unsupported
                "symbolic radial mass currently requires Uniform(0,1) x Uniform(0,1)";
            (match radial_symbolic_threshold (IntSet.elements ids) p with
             | Some threshold ->
                 let inside = symbolic_unit_square_radial_cdf threshold in
                 [ [true], inside
                 ; [false], ExprNode (Sub (ExprNode (Const 1.0), inside)) ]
             | None ->
                 unsupported
                   "symbolic region mass currently supports one origin-centered radial predicate")
        | _ ->
            unsupported
              "symbolic region mass currently supports exactly one predicate per component"
      in
      { ids; predicates; var = Printf.sprintf "__region%d" index; regions })

let predicate_equal a b =
  a.op = b.op && compare_sym_expr a.left b.left = 0
  && compare_sym_expr a.right b.right = 0

let membership component predicate =
  let n = List.length component.regions in
  let pred_index =
    match list_find_index (predicate_equal predicate) component.predicates with
    | Some i -> i | None -> failwith "internal generalized predicate lookup failure"
  in
  let sat =
    component.regions |> List.mapi (fun i (bits,_) -> i, List.nth bits pred_index)
    |> List.filter_map (fun (i,b) -> if b then Some i else None)
  in
  let v = ExprNode (Var component.var) in
  match sat with
  | [] -> ExprNode (BoolConst false)
  | xs when List.length xs = n -> ExprNode (BoolConst true)
  | xs when xs = List.init (List.length xs) Fun.id ->
      ExprNode (FinCmp (Lt, v, ExprNode (FinConst (List.length xs, n)), n, false))
  | xs ->
      let eq i = ExprNode (FinEq (v, ExprNode (FinConst (i,n)), n)) in
      List.fold_left (fun acc i -> ExprNode (Or (acc, eq i)))
        (eq (List.hd xs)) (List.tl xs)

let transform (root : expr) : expr option =
  let analysis = analyze root in
  (* Non-uniform compound kernels already have an exact legacy CDF route (for
     example normalized Gaussian sums).  Leave those untouched.  Once a
     component is made solely of supported uniforms, however, this pass owns
     it and an unsupported predicate is an explicit error, never an
     approximation or silent fallback. *)
  let seeded_ids =
    List.fold_left (fun ids p -> IntSet.union ids p.deps)
      IntSet.empty analysis.seeds
  in
  let supported_uniform id =
    match List.find_opt (fun s -> s.id = id) analysis.samples with
    | Some {lo=Some _; hi=Some _; _} -> true
    | _ -> false
  in
  let supported_symbolic_seed p =
    let ids = IntSet.elements p.deps in
    match ids with
    | [_; _] ->
        List.for_all supported_uniform ids
        && (match radial_symbolic_threshold ids p with Some _ -> true | None -> false)
    | _ -> false
  in
  let has_unsupported_symbolic_seed =
    List.exists
      (fun p ->
         (contains_parameter p.left || contains_parameter p.right)
         && not (supported_symbolic_seed p))
      analysis.seeds
  in
  let components =
    if has_unsupported_symbolic_seed
       || not (IntSet.for_all supported_uniform seeded_ids)
    then []
    else build_components analysis
  in
  if components = [] then None else
  let claimed = List.fold_left (fun s c -> IntSet.union s c.ids) IntSet.empty components in
  let next_id = ref 0 in
  let need context = function
    | Some x -> x | None -> unsupported "continuous value remains required by %s" context
  in
  let find_component p =
    List.find_opt (fun c -> not (IntSet.is_empty (IntSet.inter c.ids p.deps))) components
  in

  (* Rewalk the AST and rewrite the semantically equivalent program. Each component is wrapped in a Let __regionN = DiscreteCase [(0,p0);(1,p1);…] *)
  let rec rewrite env (ExprNode node) =
    let rec binary name ctor a b =
      let a,sa = rewrite env a and b,sb = rewrite env b in
      let sym = match sa,sb with Some x,Some y -> Some (ctor x y) | _ -> None in
      if (match sym with
          | Some s -> not (IntSet.is_empty (IntSet.inter claimed (deps s)))
          | None -> false)
      then None, sym else Some (ExprNode (ctor_expr name (need name a) (need name b))), sym
    and ctor_expr name a b = match name with
      | "addition" -> Add(a,b) | "subtraction" -> Sub(a,b)
      | "multiplication" -> Mul(a,b) | "division" -> Div(a,b)
      | _ -> failwith "internal arithmetic constructor"
    in
    match node with
    | Const f -> Some (ExprNode (Const f)), Some (SConst f)
    | Var x ->
        let provenance =
          match StringMap.find_opt x env with
          | Some provenance -> provenance
          | None -> Some (SParam x)
        in
        Some (ExprNode (Var x)), provenance
    | Sample d ->
        let id = !next_id in incr next_id;
        let s = SSample id in
        if IntSet.mem id claimed then None, Some s else Some (ExprNode (Sample d)), Some s
    | Add(a,b) -> binary "addition" sadd a b
    | Sub(a,b) -> binary "subtraction" (fun x y -> sadd x (SNeg y)) a b
    | Mul(a,b) -> binary "multiplication" smul a b
    | Div(a,b) -> binary "division" (fun x y -> SDiv(x,y)) a b
    | Let(x,a,b) ->
        let ra,sa = rewrite env a in
        let rb,sb = rewrite (StringMap.add x sa env) b in
        (match ra with None -> rb,sb | Some a -> Some (ExprNode (Let(x,a,need "let body" rb))), sb)
    | Cmp(op,a,b,flipped) ->
        let ra,sa = rewrite env a and rb,sb = rewrite env b in
        (match sa,sb with
         | Some left, Some right ->
             let p = {op;left;right;deps=IntSet.union (deps left) (deps right)} in
             (match find_component p with
              | Some c -> Some (membership c p), None
              | None -> Some (ExprNode (Cmp(op,need "comparison" ra,need "comparison" rb,flipped))), None)
         | _ -> Some (ExprNode (Cmp(op,need "comparison" ra,need "comparison" rb,flipped))), None)
    | If(c,t,f) ->
        let c,_=rewrite env c and t,_=rewrite env t and f,_=rewrite env f in
        Some (ExprNode (If(need "if condition" c,need "if branch" t,need "if branch" f))),None
    | Pair(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(Pair(need "pair" a,need "pair" b))),None
    | And(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(And(need "and" a,need "and" b))),None
    | Or(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(Or(need "or" a,need "or" b))),None
    | Not a -> let a,_=rewrite env a in Some(ExprNode(Not(need "not" a))),None
    | First a -> let a,_=rewrite env a in Some(ExprNode(First(need "fst" a))),None
    | Second a -> let a,_=rewrite env a in Some(ExprNode(Second(need "snd" a))),None
    | Observe a -> let a,_=rewrite env a in Some(ExprNode(Observe(need "observe" a))),None
    | Ref a -> let a,_=rewrite env a in Some(ExprNode(Ref(need "ref" a))),None
    | Deref a -> let a,_=rewrite env a in Some(ExprNode(Deref(need "deref" a))),None
    | Reset a -> let a,_=rewrite env a in Some(ExprNode(Reset(need "reset" a))),None
    | Fun(x,a) -> let a,_=rewrite (StringMap.add x None env) a in Some(ExprNode(Fun(x,need "function" a))),None
    | Fix(f,x,a) -> let env=StringMap.add f None (StringMap.add x None env) in let a,_=rewrite env a in Some(ExprNode(Fix(f,x,need "fix" a))),None
    | Shift(k,a) -> let a,_=rewrite (StringMap.add k None env) a in Some(ExprNode(Shift(k,need "shift" a))),None
    | FuncApp(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(FuncApp(need "application" a,need "application" b))),None
    | FinCmp(op,a,b,n,f) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(FinCmp(op,need "finite comparison" a,need "finite comparison" b,n,f))),None
    | FinEq(a,b,n) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(FinEq(need "finite equality" a,need "finite equality" b,n))),None
    | Cons(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(Cons(need "list" a,need "list" b))),None
    | Assign(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(Assign(need "assignment" a,need "assignment" b))),None
    | Seq(a,b) -> let a,_=rewrite env a and b,_=rewrite env b in Some(ExprNode(Seq(need "sequence" a,need "sequence" b))),None
    | DiscreteCase cases ->
        Some(ExprNode(DiscreteCase(List.map(fun(a,p)->let a,_=rewrite env a and p,_=rewrite env p in need "discrete branch" a,need "probability" p)cases))),None
    | MatchList(a,b,y,ys,c) ->
        let a,_=rewrite env a and b,_=rewrite env b in
        let c,_=rewrite(StringMap.add y None(StringMap.add ys None env))c in
        Some(ExprNode(MatchList(need "match" a,need "match" b,y,ys,need "match" c))),None
    | SpecialFunc(name,args) ->
        Some(ExprNode(SpecialFunc(name,List.map(fun a->let a,_=rewrite env a in need "special function" a)args))),None
    | Cdf _ | CdfJvp _ | CdfVjp _ | CdfExpr _ -> unsupported "generated CDF occurs inside a generalized component"
    | BoolConst b -> Some(ExprNode(BoolConst b)),None
    | FinConst(k,n) -> Some(ExprNode(FinConst(k,n))),None
    | Nil -> Some(ExprNode Nil),None | Unit -> Some(ExprNode Unit),None
    | RuntimeError s -> Some(ExprNode(RuntimeError s)),None
  in
  let body,_ = rewrite StringMap.empty root in
  let body = need "program result" body in
  let result = List.fold_right (fun c body ->
    let n = List.length c.regions in
    let cases = List.mapi (fun i (_,p) -> ExprNode(FinConst(i,n)),p) c.regions in
    ExprNode(Let(c.var,ExprNode(DiscreteCase cases),body))) components body
  in Some result
