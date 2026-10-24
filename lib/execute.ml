(** Call-by-value symbolic execution, with a persistent store per path. This
    implements the symbolic operational semantics; path bookkeeping lives in
    [Path]. *)
open Ast
open Path
module S = Symbolic

type config = { max_steps : int; max_paths : int }
type result = { paths : Value.t outcome list; complete : bool }

let default_config = { max_steps = 10000; max_paths = 10000 }
exception Path_limit = Path.Path_limit

let arith = function Add -> S.Add | Sub -> S.Sub | Mul -> S.Mul | Div -> S.Div
let comparison = function Lt -> S.Lt | Le -> S.Le | Eq -> S.Eq

(* Coercions *)
let scalar t = return (Value.Scalar t)
let to_scalar = function Value.Scalar t -> return t | _ -> fail "Expected a scalar value"
let to_number v =
  let* t = to_scalar v in
  if S.is_boolean t || (match t with S.Finite _ -> true | _ -> false)
  then fail "Expected a numeric value" else return t
let to_boolean v =
  let* t = to_scalar v in
  match t with
  | S.Parameter _ -> return t
  | _ when S.is_boolean t -> return t
  | _ -> fail "Expected a Boolean condition"
let to_finite n v =
  let* t = to_scalar v in
  match t with
  | S.Finite (k,m) when m=n -> return k
  | _ -> fail "Finite comparison has incompatible operands"

let sample x d params =
  let* id = draw x d params in
  match Distribution.outcomes d params with
  | None -> scalar (Option.value (Distribution.point_mass d params) ~default:(S.Sample id))
  | Some outcomes ->
      let possible = List.filter (fun (_,weight) -> weight <> S.Number 0.) outcomes in
      let* v = fork x (List.map (fun (v,_) -> S.binary S.Eq (S.Sample id) v, v) possible) in
      scalar v

let rec eval x env expression =
  let* () = tick x in
  let eval_here = eval x env in
  let number e = let* v = eval_here e in to_number v in
  let boolean e = let* v = eval_here e in to_boolean v in
  match expression with
  | Var name -> return (Option.value (List.assoc_opt name env) ~default:(Value.Scalar (S.Parameter name)))
  | Const n ->
      if S.finite_number (S.Number n) then scalar (S.Number n) else fail "Non-finite literal"
  | Bool b -> scalar (S.Boolean b)
  | Unit -> return Value.Unit
  | Nil -> return Value.Nil
  | Finite (k,n) -> scalar (S.Finite (k,n))
  | Arith (op,a,b) ->
      let* a = number a in
      let* b = number b in
      let* () = if op=Div
        then require "Division by zero" (S.negate (S.binary S.Eq b (S.Number 0.)))
        else return () in
      let t = S.binary (arith op) a b in
      if S.finite_number t then scalar t else fail "Non-finite arithmetic result"
  | Compare (op,a,b) ->
      let* a = number a in
      let* b = number b in
      scalar (S.binary (comparison op) a b)
  | Finite_compare (op,n,a,b) ->
      let* a = let* v = eval_here a in to_finite n v in
      let* b = let* v = eval_here b in to_finite n v in
      scalar (S.Boolean (match op with Lt -> a<b | Le -> a<=b | Eq -> a=b))
  | Not a -> let* c = boolean a in scalar (S.negate c)
  | And (a,b) ->
      let* c = boolean a in
      let* yes = branch x c in
      if yes then let* c = boolean b in scalar c else scalar (S.Boolean false)
  | Or (a,b) ->
      let* c = boolean a in
      let* yes = branch x c in
      if yes then scalar (S.Boolean true) else let* c = boolean b in scalar c
  | If (c,a,b) ->
      let* c = boolean c in
      let* yes = branch x c in
      eval_here (if yes then a else b)
  | Let (name,a,b) -> let* v = eval_here a in eval x ((name,v)::env) b
  | Fun (param,body) -> return (Value.Closure {self=None; param; body; env})
  | Fix (self,param,body) -> return (Value.Closure {self=Some self; param; body; env})
  | Apply (f,a) ->
      let* f = eval_here f in
      let* a = eval_here a in
      (match f with
       | Value.Closure c ->
           let env = match c.self with Some name -> (name,f)::c.env | None -> c.env in
           eval x ((c.param,a)::env) c.body
       | _ -> fail "Application of a non-function")
  | Pair (a,b) ->
      let* a = eval_here a in
      let* b = eval_here b in
      return (Value.Pair (a,b))
  | First e ->
      let* v = eval_here e in
      (match v with Value.Pair (a,_) -> return a | _ -> fail "fst expects a pair")
  | Second e ->
      let* v = eval_here e in
      (match v with Value.Pair (_,b) -> return b | _ -> fail "snd expects a pair")
  | Cons (a,b) ->
      let* a = eval_here a in
      let* b = eval_here b in
      (match b with
       | Value.Nil | Value.Cons _ -> return (Value.Cons (a,b))
       | _ -> fail "List tail must be a list")
  | Match_list (e,nil,head,tail,cons) ->
      let* v = eval_here e in
      (match v with
       | Value.Nil -> eval_here nil
       | Value.Cons (a,b) -> eval x ((head,a)::(tail,b)::env) cons
       | _ -> fail "match expects a list")
  | Ref e ->
      let* v = eval_here e in
      let* id = alloc v in
      return (Value.Location id)
  | Deref e ->
      let* v = eval_here e in
      (match v with Value.Location id -> read id | _ -> fail "Dereference expects a reference")
  | Assign (a,b) ->
      let* r = eval_here a in
      let* v = eval_here b in
      (match r with
       | Value.Location id -> let* () = write id v in return Value.Unit
       | _ -> fail "Assignment expects a reference")
  | Seq (a,b) -> let* _ = eval_here a in eval_here b
  | Sample (d,args) ->
      let* params = all (List.map number args) in
      sample x d params
  | Observe e ->
      let* c = boolean e in
      let* () = observe c in
      let* ok = branch x c in
      if ok then return Value.Unit else stop Rejected

(* Materialize returned Boolean queries too, not only branch conditions. *)
let rec materialize x = function
  | Value.Scalar t when S.is_boolean t ->
      let* b = branch x t in scalar (S.Boolean b)
  | Value.Pair (a,b) ->
      let* a = materialize x a in
      let* b = materialize x b in
      return (Value.Pair (a,b))
  | Value.Cons (a,b) ->
      let* a = materialize x a in
      let* b = materialize x b in
      return (Value.Cons (a,b))
  | v -> return v

let run ?(config=default_config) ?(parameters=[]) expression =
  if config.max_steps < 1 || config.max_paths < 1
  then invalid_arg "Execution bounds must be positive";
  let x = exploration ~max_steps:config.max_steps ~max_paths:config.max_paths in
  let env = List.map (fun (name,n) ->
    if not (S.finite_number (S.Number n)) then invalid_arg "Non-finite parameter";
    name,Value.Scalar (S.Number n)) parameters in
  let paths = (let* v = eval x env expression in materialize x v) Path.empty in
  let complete = List.for_all (function
    | Returned _ | Stopped (_,Rejected) -> true | _ -> false) paths
  in {paths;complete}
