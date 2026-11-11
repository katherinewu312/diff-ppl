(** Symbolic evaluation and boundary extraction. Conditional-valued guards
    are lifted at value level, then eliminated under refined path conditions.
    Source operands remain eager; lifting never repeats a sampling operation. *)
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
  let condition path value =
    let numeric_contexts=Solver.Terms.create 16 and boolean_contexts=Solver.Terms.create 16 in
    let memo contexts path value compute =
      let values=match Solver.Terms.find_opt contexts path with
        | Some values -> values
        | None -> let values=Solver.Terms.create 32 in
            Solver.Terms.add contexts path values;values in
      match Solver.Terms.find_opt values value with
      | Some result -> result
      | None -> let result=compute () in Solver.Terms.add values value result;result
    in
    (* These are transformations of values, not source evaluation. Both source
       operands have already executed before their choices are distributed. *)
    let rec choose path c yes no = match c with
      | S.Boolean true -> yes path
      | Boolean false -> no path
      | Ite (d,a,b) ->
          choose path d (fun path -> choose path a yes no)
            (fun path -> choose path b yes no)
      | _ ->
          if entailed path c then yes path
          else if entailed path (S.negate c) then no path
          else S.Ite (c,yes (S.and_ path c),no (S.and_ path (S.negate c)))
    and lift path op a b = match a,b with
      | S.Ite (c,x,y),_ ->
          choose path c (fun path -> lift path op x b) (fun path -> lift path op y b)
      | _,S.Ite (c,x,y) ->
          choose path c (fun path -> lift path op a x) (fun path -> lift path op a y)
      | _ -> op a b
    and real path value = memo numeric_contexts path value (fun () -> match value with
      | S.Number _ | Parameter _ | Sample _ -> value
      | Arith (op,a,b) -> lift path (S.arith op) (real path a) (real path b)
      | Ite (c,a,b) ->
          choose path (boolean path c) (fun path -> real path a) (fun path -> real path b)
      | _ -> error "Expected a numeric symbolic value")
    and boolean path value = memo boolean_contexts path value (fun () -> match value with
      | S.Boolean _ | Parameter _ -> value
      | Compare (op,a,b) -> lift path (S.comparison op) (real path a) (real path b)
      | Not a ->
          let rec negate = function
            | S.Ite (c,a,b) -> S.Ite (c,negate a,negate b)
            | a -> S.negate a in
          negate (boolean path a)
      | And (a,b) -> lift path S.and_ (boolean path a) (boolean path b)
      | Or (a,b) -> lift path S.or_ (boolean path a) (boolean path b)
      | Ite (c,a,b) ->
          choose path (boolean path c) (fun path -> boolean path a) (fun path -> boolean path b)
      | _ -> error "Expected a symbolic Boolean condition")
    in boolean path value
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
    | Compare (op,a,b) -> two a b (fun a b -> condition path (S.comparison op (numeric a) (numeric b)))
    (* The paper's operator rule is eager: both operands use the same pi. *)
    | And (a,b) -> two a b (fun a b -> condition path (S.And (a,b)))
    | Or (a,b) -> two a b (fun a b -> condition path (S.Or (a,b)))
    | Not a -> let v,b=here a in condition path (S.Not v),b
    | If (c,a,b) ->
        let c,bc=here c in
        let v,boundaries=branch env path (condition path c) a b in
        v,S.union bc boundaries
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
  (* S-IfIte / True / False consume Boolean choices without evaluating e0
     again. Leaf conditions use the ordinary S-If family. No fresh variable
     is needed internally, so the implementation also avoids capture. *)
  and branch env path c yes no =
    match c with
    | S.Ite (selector,a,b) ->
        split path selector (fun path -> branch env path a yes no)
          (fun path -> branch env path b yes no)
    | _ -> split path c (fun path -> eval env path yes) (fun path -> eval env path no)
  and split path c yes no =
    if entailed path c then yes path
    else if entailed path (S.negate c) then no path
    else
      let va,ba=yes (S.and_ path c) in
      let vb,bb=no (S.and_ path (S.negate c)) in
      S.Ite (c,va,vb),S.union ba (S.union bb (S.record path c va vb))
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
