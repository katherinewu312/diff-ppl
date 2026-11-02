(** Literal implementation of the judgments in tex/main.tex, Section Analysis.
    [eval] implements =>, [apply] implements the auxiliary downward arrow.
    No path enumeration, probability integration, or AD is performed. *)
open Ast
module S = Symbolic

exception Error of string
let error message = raise (Error message)
type result = { value : S.t; candidates : S.boundary list; samples : S.sample list }

let run ?(parameters=[]) ~solver expression =
  let samples=ref [] and next_sample=ref 1 in
  let fresh distribution =
    let id= !next_sample in incr next_sample;
    samples := !samples @ [{S.id;distribution}]; S.Sample id
  in
  let entailed path condition =
    match condition with
    | S.Boolean b -> b
    | _ -> Solver.entails solver !samples path condition
  in
  let ensure_feasible path = match path with
    | S.Boolean true -> ()
    | S.Boolean false -> error "No analysis rule for an infeasible incoming path"
    | _ when Solver.query solver !samples path=Solver.Unsat ->
        error "No analysis rule for an infeasible incoming path"
    | _ -> ()
  in
  let numeric = function
    | S.Boolean _ | Compare _ | And _ | Or _ | Not _
    | Closure _ | Pair _ | Cons _ | Nil | Unit -> error "Expected a numeric symbolic value"
    | value -> value
  in
  let rec condition = function
    | (S.Boolean _ | Parameter _ | Compare _) as v -> v
    | Not v -> S.negate (condition v)
    | And (a,b) -> S.and_ (condition a) (condition b)
    | Or (a,b) -> S.or_ (condition a) (condition b)
    | _ -> error "The paper's condition grammar has no rule for this value (for example, an ite of Boolean values)"
  in
  let rec eval env path expression =
    ensure_feasible path;
    let here=eval env path in
    let two a b combine =
      let va,ba=here a in let vb,bb=here b in combine va vb,S.union ba bb in
    match expression with
    | Var x -> (match List.assoc_opt x env with
        | Some v -> v,[] | None -> error ("Unbound variable " ^ x ^ "; declare free inputs with --param " ^ x))
    | Const n -> S.number n,[] | Bool b -> S.Boolean b,[]
    | Unit -> S.Unit,[] | Nil -> S.Nil,[]
    | Fun (param,body) -> S.Closure {env;self=None;param;body},[]
    | Fix (self,param,body) -> S.Closure {env;self=Some self;param;body},[]
    | Let (x,a,b) ->
        let va,ba=here a in let vb,bb=eval ((x,va)::env) path b in vb,S.union ba bb
    | Arith (op,a,b) -> two a b (fun a b -> S.arith op (numeric a) (numeric b))
    | Compare (op,a,b) -> two a b (fun a b -> S.comparison op (numeric a) (numeric b))
    (* The paper's operator rule is eager: both operands use the same pi. *)
    | And (a,b) -> two a b (fun a b -> S.and_ (condition a) (condition b))
    | Or (a,b) -> two a b (fun a b -> S.or_ (condition a) (condition b))
    | Not a -> let v,b=here a in S.negate (condition v),b
    | If (c,a,b) ->
        let c,bc=here c in let c=condition c in
        if entailed path c then let v,b=here a in v,S.union bc b
        else if entailed path (S.negate c) then let v,b=here b in v,S.union bc b
        else
          let va,ba=eval env (S.and_ path c) a in
          let vb,bb=eval env (S.and_ path (S.negate c)) b in
          S.Ite (c,va,vb), S.union bc (S.union ba (S.union bb (S.record path c va vb)))
    | Sample (Uniform,[a;b]) ->
        let a,ba=here a in let b,bb=here b in
        let a=numeric a and b=numeric b in let s=fresh Uniform in
        S.arith Add a (S.arith Mul (S.arith Sub b a) s),S.union ba bb
    | Sample (Gaussian,[mu;sigma]) ->
        let mu,bm=here mu in let sigma,bs=here sigma in
        let mu=numeric mu and sigma=numeric sigma in let s=fresh Gaussian in
        S.arith Add mu (S.arith Mul sigma s),S.union bm bs
    | Sample (d,_) -> error (distribution_name d ^ " requires two arguments")
    | Apply (f,a) ->
        let f,bf=here f in let a,ba=here a in
        let value,b=apply path f a in value,S.union bf (S.union ba b)
    | Pair (a,b) -> two a b (fun a b -> S.Pair (a,b))
    | Cons (a,b) -> two a b (fun a b -> S.Cons (a,b))
    | First e -> let v,b=here e in let v,b'=project path true v in v,S.union b b'
    | Second e -> let v,b=here e in let v,b'=project path false v in v,S.union b b'
    | Match_list (e,nil,head,tail,cons) ->
        let v,b=here e in let v,b'=match_list env path v nil head tail cons in v,S.union b b'
  and apply path fn argument =
    ensure_feasible path;
    match fn with
    | S.Closure c ->
        let env=match c.self with None -> c.env | Some f -> (f,fn)::c.env in
        eval ((c.param,argument)::env) path c.body
    | Ite (c,a,b) ->
        if entailed path c then apply path a argument
        else if entailed path (S.negate c) then apply path b argument
        else
          let va,ba=apply (S.and_ path c) a argument in
          let vb,bb=apply (S.and_ path (S.negate c)) b argument in
          S.Ite (c,va,vb),S.union ba (S.union bb (S.record path c va vb))
    | _ -> error "Application requires a closure or an ite of closures"
  and project path first value =
    ensure_feasible path;
    match value with
    | S.Pair (a,b) -> (if first then a else b),[]
    | Ite (c,a,b) ->
        let va,ba=project (S.and_ path c) first a in
        let vb,bb=project (S.and_ path (S.negate c)) first b in
        S.Ite (c,va,vb),S.union ba (S.union bb (S.record path c va vb))
    | _ -> error "Projection requires a pair or an ite of pairs"
  and match_list env path value nil head tail cons =
    ensure_feasible path;
    match value with
    | S.Nil -> eval env path nil
    | Cons (a,b) -> eval ((head,a)::(tail,b)::env) path cons
    | Ite (c,a,b) ->
        let va,ba=match_list env (S.and_ path c) a nil head tail cons in
        let vb,bb=match_list env (S.and_ path (S.negate c)) b nil head tail cons in
        S.Ite (c,va,vb),S.union ba (S.union bb (S.record path c va vb))
    | _ -> error "match requires a list or an ite of lists"
  in
  let value,candidates=eval parameters S.truth expression in
  {value;candidates;samples= !samples}
