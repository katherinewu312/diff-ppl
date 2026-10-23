(** Call-by-value symbolic execution, with a persistent store per path. *)
open Ast
module S = Symbolic
module Store = Map.Make(Int)

type value =
  | Scalar of S.term | Pair_value of value * value
  | Nil_value | Cons_value of value * value | Unit_value | Location of int
  | Closure of string * expr * env
  | Recursive of string * string * expr * env
and env = (string * value) list

type kernel =
  | Distribution of string * S.term list
  | Categorical of S.term list
  | Bernoulli of S.term

type sampling = { id : int; kernel : kernel }
type state = {
  constraints : S.term list;
  observations : S.term list;
  requirements : S.term list;
  samplings : sampling list;
  store : value Store.t;
  next_location : int;
  steps : int;
}

type stop = Rejected | Recursion_limit | Step_limit | Runtime_error of string
type outcome = Returned of state * value | Stopped of state * stop
type config = { max_recursion : int; max_steps : int; max_paths : int }
type result = { paths : outcome list; complete : bool }

let default_config = { max_recursion = 32; max_steps = 10000; max_paths = 10000 }
exception Path_limit of int
exception Eval_error of string
let error msg = raise (Eval_error msg)

let empty_state = {
  constraints=[]; observations=[]; requirements=[]; samplings=[];
  store=Store.empty; next_location=0; steps=0;
}

let scalar = function Scalar t -> t | _ -> error "Expected a scalar value"
let numeric v =
  let t = scalar v in
  if S.is_boolean t || (match t with S.Finite _ -> true | _ -> false)
  then error "Expected a numeric value" else t
let boolean v =
  let t = scalar v in
  match t with
  | S.Parameter _ -> t
  | _ when S.is_boolean t -> t
  | _ -> error "Expected a Boolean condition"

let assume state condition =
  match condition with
  | S.Boolean true -> Some state
  | S.Boolean false -> None
  | t when List.mem (S.negate t) state.constraints -> None
  | t when List.mem t state.constraints -> Some state
  | t -> Some {state with constraints=state.constraints @ [t]}

let require state term =
  match term with
  | S.Boolean true -> state
  | S.Boolean false -> error "Invalid numeric operation or distribution parameters"
  | t when List.mem t state.requirements -> state
  | t -> {state with requirements=state.requirements @ [t]}

let kernel_requirements state kernel =
  let positive s x = require s (S.binary S.Lt (S.Number 0.) x) in
  let probability s x =
    require (require s (S.binary S.Le (S.Number 0.) x))
      (S.binary S.Le x (S.Number 1.))
  in
  match kernel with
  | Bernoulli p -> probability state p
  | Categorical ps ->
      let state = List.fold_left probability state ps in
      let sum = List.fold_left (S.binary S.Add) (S.Number 0.) ps in
      (match sum with
       | S.Number n when abs_float (n -. 1.) < 1e-12 -> state
       | _ -> require state (S.binary S.Eq sum (S.Number 1.)))
  | Distribution ("uniform",[a;b]) -> require state (S.binary S.Le a b)
  | Distribution (("gaussian" | "lognormal"),[_;sigma]) -> positive state sigma
  | Distribution (("gumbel1" | "gumbel2"),[_;b]) -> positive state b
  | Distribution ("poisson",[mu]) -> require state (S.binary S.Le (S.Number 0.) mu)
  | Distribution ("binomial",[p;n]) ->
      let state = probability state p in
      let state = require state (S.binary S.Le (S.Number 0.) n) in
      (match n with
       | S.Number n when floor n <> n -> error "Binomial trial count must be integral"
       | S.Number _ -> state
       | n -> require state (S.Is_integer n))
  | Distribution (_,params) -> List.fold_left positive state params

let bind outcomes f =
  List.concat_map (function
    | Returned (s,v) -> (try f s v with Eval_error msg -> [Stopped (s,Runtime_error msg)])
    | Stopped _ as o -> [o]) outcomes

let run ?(config=default_config) ?(parameters=[]) expression =
  if config.max_recursion < 0 || config.max_steps < 1 || config.max_paths < 1
  then invalid_arg "Execution bounds must be positive (recursion may be zero)";
  let next_sample = ref 0 and leaves = ref 1 in
  let split count =
    leaves := !leaves + max 0 (count-1);
    if !leaves > config.max_paths then raise (Path_limit config.max_paths)
  in
  let fresh state kernel =
    let state = kernel_requirements state kernel in
    let id = !next_sample in incr next_sample;
    {state with samplings=state.samplings @ [{id;kernel}]}, id
  in
  let choose state condition =
    let cases =
      List.filter_map (fun b ->
        Option.map (fun s -> s,b) (assume state (if b then condition else S.negate condition)))
        [true;false]
    in split (List.length cases); cases
  in
  let rec eval depth env state (ExprNode expression) =
    if state.steps >= config.max_steps then [Stopped (state,Step_limit)] else
    let state = {state with steps=state.steps+1} in
    let ret v = [Returned (state,v)] in
    let evaluate e = eval depth env state e in
    let unary e f = bind (evaluate e) f in
    let two a b f = unary a (fun s a -> bind (eval depth env s b) (fun s b -> f s a b)) in
    let arithmetic op a b = two a b (fun s a b ->
      let a = numeric a and b = numeric b in
      let s = if op=S.Div then require s (S.negate (S.binary S.Eq b (S.Number 0.))) else s in
      let t = S.binary op a b in
      if not (S.finite_number t) then error "Non-finite arithmetic result";
      [Returned (s,Scalar t)])
    in
    try match expression with
    | Var x -> ret (Option.value (List.assoc_opt x env) ~default:(Scalar (S.Parameter x)))
    | Const x ->
        if not (S.finite_number (S.Number x)) then error "Non-finite literal";
        ret (Scalar (S.Number x))
    | BoolConst b -> ret (Scalar (S.Boolean b))
    | Unit -> ret Unit_value | Nil -> ret Nil_value
    | FinConst (k,n) -> ret (Scalar (S.Finite (k,n)))
    | Let (x,a,b) -> unary a (fun s v -> eval depth ((x,v)::env) s b)
    | Fun (x,b) -> ret (Closure (x,b,env))
    | Fix (f,x,b) -> ret (Recursive (f,x,b,env))
    | FuncApp (f,a) -> two f a (fun s f a -> match f with
        | Closure (x,b,captured) -> eval depth ((x,a)::captured) s b
        | Recursive (name,x,b,captured) ->
            if depth >= config.max_recursion then [Stopped (s,Recursion_limit)]
            else eval (depth+1) ((x,a)::(name,f)::captured) s b
        | _ -> error "Application of a non-function")
    | If (c,a,b) -> unary c (fun s v ->
        List.concat_map (fun (s,yes) -> eval depth env s (if yes then a else b))
          (choose s (boolean v)))
    | And (a,b) | Or (a,b) ->
        let is_and = match expression with And _ -> true | _ -> false in
        unary a (fun s v ->
          List.concat_map (fun (s,yes) ->
            if yes=is_and then
              bind (eval depth env s b) (fun s v -> [Returned (s,Scalar (boolean v))])
            else [Returned (s,Scalar (S.Boolean yes))]) (choose s (boolean v)))
    | Not a -> unary a (fun s v -> [Returned (s,Scalar (S.negate (boolean v)))])
    | Add (a,b) -> arithmetic S.Add a b | Sub (a,b) -> arithmetic S.Sub a b
    | Mul (a,b) -> arithmetic S.Mul a b | Div (a,b) -> arithmetic S.Div a b
    | Cmp (op,a,b,_) -> two a b (fun s a b ->
        [Returned (s,Scalar (S.binary (if op=Lt then S.Lt else S.Le) (numeric a) (numeric b)))])
    | FinCmp (op,a,b,n,_) -> two a b (fun s a b ->
        match scalar a,scalar b with
        | S.Finite (a,m),S.Finite (b,k) when m=n && k=n ->
            [Returned (s,Scalar (S.Boolean (if op=Lt then a<b else a<=b)))]
        | _ -> error "Finite comparison has incompatible operands")
    | FinEq (a,b,n) -> two a b (fun s a b ->
        match scalar a,scalar b with
        | S.Finite (_,m) as a,(S.Finite (_,k) as b) when m=n && k=n ->
            [Returned (s,Scalar (S.binary S.Eq a b))]
        | _ -> error "Finite equality has incompatible operands")
    | Sample distribution ->
        let emit s name params =
          let s,id = fresh s (Distribution (name,params)) in
          let t = match name,params with
            | "uniform",[a;b] when a=b -> a
            | _ -> S.Sample id in
          [Returned (s,Scalar t)]
        in
        (match distribution with
         | Distr1 (kind,a) -> unary a (fun s a -> emit s (distribution1_name kind) [numeric a])
         | Distr2 (kind,a,b) -> two a b (fun s a b -> emit s (distribution2_name kind) [numeric a;numeric b]))
    | Flip p -> unary p (fun s p ->
        let p = numeric p in
        let s,id = fresh s (Bernoulli p) in
        let cases = List.filter_map (fun (b,weight) ->
          if weight=S.Number 0. then None else
          Option.map (fun s -> Returned (s,Scalar (S.Boolean b)))
            (assume s (S.binary S.Eq (S.Sample id) (S.Boolean b))))
          [true,p;false,S.binary S.Sub (S.Number 1.) p]
        in split (List.length cases); cases)
    | DiscreteCase cases ->
        let rec probabilities s acc = function
          | [] ->
              let cases = List.rev acc in
              let s,id = fresh s (Categorical (List.map snd cases)) in
              let paths = List.filter_map (fun (index,(body,p)) ->
                if p=S.Number 0. then None else
                Option.map (fun s -> s,body)
                  (assume s (S.binary S.Eq (S.Sample id) (S.Finite (index,List.length cases)))))
                (List.mapi (fun i c -> i,c) cases)
              in split (List.length paths);
              List.concat_map (fun (s,body) -> eval depth env s body) paths
          | (body,p)::rest ->
              bind (eval depth env s p) (fun s p -> probabilities s ((body,numeric p)::acc) rest)
        in probabilities state [] cases
    | Observe e -> unary e (fun s v ->
        let condition = boolean v in
        let s = {s with observations=s.observations @ [condition]} in
        List.map (fun (s,yes) ->
          if yes then Returned (s,Unit_value) else Stopped (s,Rejected)) (choose s condition))
    | Pair (a,b) -> two a b (fun s a b -> [Returned (s,Pair_value (a,b))])
    | First a -> unary a (fun s -> function
        | Pair_value (a,_) -> [Returned (s,a)] | _ -> error "fst expects a pair")
    | Second a -> unary a (fun s -> function
        | Pair_value (_,b) -> [Returned (s,b)] | _ -> error "snd expects a pair")
    | Cons (a,b) -> two a b (fun s a b -> match b with
        | Nil_value | Cons_value _ -> [Returned (s,Cons_value (a,b))]
        | _ -> error "List tail must be a list")
    | MatchList (e,nil,x,xs,cons) -> unary e (fun s -> function
        | Nil_value -> eval depth env s nil
        | Cons_value (a,b) -> eval depth ((x,a)::(xs,b)::env) s cons
        | _ -> error "match expects a list")
    | Ref e -> unary e (fun s v ->
        let id = s.next_location in
        [Returned ({s with next_location=id+1;store=Store.add id v s.store},Location id)])
    | Deref e -> unary e (fun s -> function
        | Location id -> [Returned (s,Store.find id s.store)]
        | _ -> error "Dereference expects a reference")
    | Assign (a,b) -> two a b (fun s a b -> match a with
        | Location id -> [Returned ({s with store=Store.add id b s.store},Unit_value)]
        | _ -> error "Assignment expects a reference")
    | Seq (a,b) -> unary a (fun s _ -> eval depth env s b)
    with Eval_error msg -> [Stopped (state,Runtime_error msg)]
  in
  (* Materialize returned Boolean queries too, not only branch conditions. *)
  let rec materialize s = function
    | Scalar t when S.is_boolean t ->
        List.map (fun (s,b) -> Returned (s,Scalar (S.Boolean b))) (choose s t)
    | Pair_value (a,b) ->
        bind (materialize s a) (fun s a ->
          bind (materialize s b) (fun s b -> [Returned (s,Pair_value (a,b))]))
    | Cons_value (a,b) ->
        bind (materialize s a) (fun s a ->
          bind (materialize s b) (fun s b -> [Returned (s,Cons_value (a,b))]))
    | v -> [Returned (s,v)]
  in
  let env = List.map (fun (name,n) ->
    if not (S.finite_number (S.Number n)) then invalid_arg "Non-finite parameter";
    name,Scalar (S.Number n)) parameters in
  let paths = bind (eval 0 env empty_state expression) materialize in
  let complete = List.for_all (function
    | Returned _ | Stopped (_,Rejected) -> true | _ -> false) paths
  in {paths;complete}
