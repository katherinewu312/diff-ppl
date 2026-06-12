open Ast

module StringMap = Map.Make(String)

(* This is very preliminary so far. It simplies raw AD dual programs, giving the tuple (expected, derivative).
So far:

Constant-folds arithmetic:
1 + 2 -> 3
x + 0 -> x
x * 1 -> x
x * 0 -> 0
x / 1 -> x
x - x -> 0

Simplifies pair projections:
fst (a, b) -> a
snd (a, b) -> b

Evaluates known finite comparisons:
0#2 <#2 1#2 -> true
1#2 <#2 1#2 -> false
0#2 ==#2 0#2 -> true

Simplifies conditionals with known conditions:
if true then e1 else e2 -> e1
if false then e1 else e2 -> e2

Inlines very simple let bindings:
finite constants
float constants
booleans
unit/nil
simple pairs of those
*)

let node e = ExprNode e
let mk_const f = node (Const f)
let mk_bool b = node (BoolConst b)
let mk_pair a b = node (Pair (a, b))
let mk_first e =
  match e with
  | ExprNode (Pair (a, _)) -> a
  | _ -> node (First e)
let mk_second e =
  match e with
  | ExprNode (Pair (_, b)) -> b
  | _ -> node (Second e)

let const_value = function
  | ExprNode (Const f) -> Some f
  | _ -> None

let is_zero = function
  | ExprNode (Const f) -> f = 0.0
  | _ -> false

let is_one = function
  | ExprNode (Const f) -> f = 1.0
  | _ -> false

let mk_add a b =
  match const_value a, const_value b with
  | Some x, Some y -> mk_const (x +. y)
  | Some 0.0, _ -> b
  | _, Some 0.0 -> a
  | _ -> node (Add (a, b))

let mk_sub a b =
  match const_value a, const_value b with
  | Some x, Some y -> mk_const (x -. y)
  | _, Some 0.0 -> a
  | _ when a = b -> mk_const 0.0
  | _ -> node (Sub (a, b))

let mk_mul a b =
  match const_value a, const_value b with
  | Some x, Some y -> mk_const (x *. y)
  | Some 0.0, _ | _, Some 0.0 -> mk_const 0.0
  | Some 1.0, _ -> b
  | _, Some 1.0 -> a
  | Some (-1.0), _ -> mk_sub (mk_const 0.0) b
  | _, Some (-1.0) -> mk_sub (mk_const 0.0) a
  | _ -> node (Mul (a, b))

let mk_div a b =
  match const_value a, const_value b with
  | Some x, Some y when y <> 0.0 -> mk_const (x /. y)
  | Some 0.0, _ -> mk_const 0.0
  | _, Some 1.0 -> a
  | _ when a = b -> mk_const 1.0
  | _ -> node (Div (a, b))

let bool_value = function
  | ExprNode (BoolConst b) -> Some b
  | _ -> None

let fin_value = function
  | ExprNode (FinConst (k, n)) -> Some (k, n)
  | _ -> None

let inlineable = function
  | ExprNode (Const _ | BoolConst _ | FinConst _ | Unit | Nil) -> true
  | ExprNode (Pair (a, b)) ->
      (match a, b with
       | ExprNode (Const _ | BoolConst _ | FinConst _ | Unit | Nil),
         ExprNode (Const _ | BoolConst _ | FinConst _ | Unit | Nil) -> true
       | _ -> false)
  | _ -> false

let remove_many names env =
  List.fold_left (fun acc x -> StringMap.remove x acc) env names

let rec expr e =
  expr_env StringMap.empty e

and expr_env env (ExprNode e) =
  match e with
  | Var x ->
      (match StringMap.find_opt x env with
       | Some v -> v
       | None -> node (Var x))
  | Const f -> mk_const f
  | BoolConst b -> mk_bool b
  | Let (x, e1, e2) ->
      let e1' = expr_env env e1 in
      if inlineable e1' then
        expr_env (StringMap.add x e1' env) e2
      else
        node (Let (x, e1', expr_env (StringMap.remove x env) e2))
  | Sample d -> node (Sample (sample_env env d))
  | DistrCase cases ->
      node (DistrCase (List.map (fun (b, p) -> (expr_env env b, expr_env env p)) cases))
  | Cmp (op, e1, e2, flipped) ->
      let e1' = expr_env env e1 in
      let e2' = expr_env env e2 in
      (match op, const_value e1', const_value e2' with
       | Lt, Some x, Some y -> mk_bool (x < y)
       | Le, Some x, Some y -> mk_bool (x <= y)
       | _ -> node (Cmp (op, e1', e2', flipped)))
  | FinCmp (op, e1, e2, n, flipped) ->
      let e1' = expr_env env e1 in
      let e2' = expr_env env e2 in
      (match fin_value e1', fin_value e2' with
       | Some (k1, n1), Some (k2, n2) when n1 = n && n2 = n ->
           let result =
             match op with
             | Lt -> k1 < k2
             | Le -> k1 <= k2
           in
           mk_bool result
       | _ -> node (FinCmp (op, e1', e2', n, flipped)))
  | FinEq (e1, e2, n) ->
      let e1' = expr_env env e1 in
      let e2' = expr_env env e2 in
      (match fin_value e1', fin_value e2' with
       | Some (k1, n1), Some (k2, n2) when n1 = n && n2 = n ->
           mk_bool (k1 = k2)
       | _ -> node (FinEq (e1', e2', n)))
  | And (e1, e2) ->
      let e1' = expr_env env e1 in
      (match bool_value e1' with
       | Some false -> mk_bool false
       | Some true -> expr_env env e2
       | None -> node (And (e1', expr_env env e2)))
  | Or (e1, e2) ->
      let e1' = expr_env env e1 in
      (match bool_value e1' with
       | Some true -> mk_bool true
       | Some false -> expr_env env e2
       | None -> node (Or (e1', expr_env env e2)))
  | Not e1 ->
      let e1' = expr_env env e1 in
      (match bool_value e1' with
       | Some b -> mk_bool (not b)
       | None -> node (Not e1'))
  | If (e1, e2, e3) ->
      let e1' = expr_env env e1 in
      (match bool_value e1' with
       | Some true -> expr_env env e2
       | Some false -> expr_env env e3
       | None -> node (If (e1', expr_env env e2, expr_env env e3)))
  | Pair (e1, e2) -> mk_pair (expr_env env e1) (expr_env env e2)
  | First e1 -> mk_first (expr_env env e1)
  | Second e1 -> mk_second (expr_env env e1)
  | Fun (x, e1) ->
      node (Fun (x, expr_env (StringMap.remove x env) e1))
  | FuncApp (e1, e2) ->
      node (FuncApp (expr_env env e1, expr_env env e2))
  | LoopApp (e1, e2, n) ->
      node (LoopApp (expr_env env e1, expr_env env e2, n))
  | Fix (f, x, e1) ->
      node (Fix (f, x, expr_env (remove_many [f; x] env) e1))
  | FinConst (k, n) -> node (FinConst (k, n))
  | Observe e1 -> node (Observe (expr_env env e1))
  | Nil -> node Nil
  | Cons (e1, e2) -> node (Cons (expr_env env e1, expr_env env e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      node (MatchList
        ( expr_env env e1
        , expr_env env e_nil
        , y
        , ys
        , expr_env (remove_many [y; ys] env) e_cons ))
  | Ref e1 -> node (Ref (expr_env env e1))
  | Deref e1 -> node (Deref (expr_env env e1))
  | Assign (e1, e2) -> node (Assign (expr_env env e1, expr_env env e2))
  | Seq (e1, e2) ->
      let e1' = expr_env env e1 in
      (match e1' with
       | ExprNode Unit -> expr_env env e2
       | _ -> node (Seq (e1', expr_env env e2)))
  | Unit -> node Unit
  | RuntimeError s -> node (RuntimeError s)
  | Add (e1, e2) -> mk_add (expr_env env e1) (expr_env env e2)
  | Sub (e1, e2) -> mk_sub (expr_env env e1) (expr_env env e2)
  | Mul (e1, e2) -> mk_mul (expr_env env e1) (expr_env env e2)
  | Div (e1, e2) -> mk_div (expr_env env e1) (expr_env env e2)
  | Cdf (d, e1) -> node (Cdf (sample_env env d, expr_env env e1))
  | CdfExpr (k, e1) -> node (CdfExpr (expr_env env k, expr_env env e1))

and sample_env env = function
  | Distr1 (kind, e1) -> Distr1 (kind, expr_env env e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, expr_env env e1, expr_env env e2)
