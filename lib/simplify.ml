open Ast

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

(* The local pass performs the following rewrites:

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

Normalizes administrative higher-order code:
let f = fun x -> body in ... -> ...[fun x -> body/f]
(fun x -> body) v -> body[v/x], for syntactic values v

Reduces list pattern matches with known constructors:
match nil with ... -> nil branch
match h :: t with ... -> cons branch with h/t substituted

The separate [algebraic] pass below additionally normalizes polynomial
float expressions so post-Forward primal/tangent components can combine
like terms:
(theta * theta) + ((1 - theta) * (theta + 1)) -> 1

Inlines very simple let bindings:
variables
finite constants
float constants
booleans
functions
unit/nil
simple pairs of those
*)

let node e = ExprNode e
let mk_const f = node (Const f)
let mk_bool b = node (BoolConst b)
let mk_pair a b = node (Pair (a, b))
let rec mk_first e =
  match e with
  | ExprNode (Pair (a, _)) -> a
  | ExprNode (Let (x, e1, e2)) -> node (Let (x, e1, mk_first e2))
  | _ -> node (First e)
let rec mk_second e =
  match e with
  | ExprNode (Pair (_, b)) -> b
  | ExprNode (Let (x, e1, e2)) -> node (Let (x, e1, mk_second e2))
  | _ -> node (Second e)

let const_value = function
  | ExprNode (Const f) -> Some f
  | _ -> None

let special_value name args =
  match name, args with
  | "exp", [x] -> Some (exp x)
  | "log", [x] -> Some (log x)
  | "sqrt", [x] -> Some (sqrt x)
  | "pow", [x; y] -> Some (x ** y)
  | "erf", [x] -> Some (Gsl.Sf.erf x)
  | "atan", [x] -> Some (atan x)
  | "abs", [x] -> Some (abs_float x)
  | "beta", [x; y] -> Some (Gsl.Sf.beta x y)
  | "beta_inc", [a; b; x] -> Some (Gsl.Sf.beta_inc a b x)
  | "gamma", [x] -> Some (Gsl.Sf.gamma x)
  | "gamma_inc_P", [a; x] -> Some (Gsl.Sf.gamma_inc_P a x)
  | _ -> None

let is_zero = function
  | ExprNode (Const f) -> f = 0.0
  | _ -> false

let is_one = function
  | ExprNode (Const f) -> f = 1.0
  | _ -> false

let has_prefix s prefix =
  let n = String.length prefix in
  String.length s >= n && String.sub s 0 n = prefix

let generated_ad_name x = has_prefix x "_forward_"

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

let mk_special name args =
  match List.map const_value args with
  | values when List.for_all Option.is_some values ->
      let floats = List.map Option.get values in
      (match special_value name floats with
       | Some f -> mk_const f
       | None -> node (SpecialFunc (name, args)))
  | _ -> node (SpecialFunc (name, args))

let bool_value = function
  | ExprNode (BoolConst b) -> Some b
  | _ -> None

let fin_value = function
  | ExprNode (FinConst (k, n)) -> Some (k, n)
  | _ -> None

let union_many sets =
  List.fold_left StringSet.union StringSet.empty sets

let remove_many_set names set =
  List.fold_left (fun acc x -> StringSet.remove x acc) set names

let rec vars (ExprNode e) =
  match e with
  | Var x -> StringSet.singleton x
  | Const _ | BoolConst _ | FinConst _ | Nil | Unit | RuntimeError _ ->
      StringSet.empty
  | Let (x, e1, e2) -> StringSet.add x (union_many [vars e1; vars e2])
  | Sample d -> vars_sample d
  | DiscreteCase cases ->
      union_many (List.map (fun (b, p) -> StringSet.union (vars b) (vars p)) cases)
  | Cmp (_, e1, e2, _) | And (e1, e2) | Or (e1, e2)
  | Pair (e1, e2) | FuncApp (e1, e2)
  | FinEq (e1, e2, _) ->
      union_many [vars e1; vars e2]
  | FinCmp (_, e1, e2, _, _) | Assign (e1, e2) | Seq (e1, e2)
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2)
  | CdfExpr (e1, e2) ->
      union_many [vars e1; vars e2]
  | Not e1 | First e1 | Second e1 | Observe e1 | Ref e1 | Deref e1 ->
      vars e1
  | Reset e1 -> vars e1
  | Shift (k, e1) -> StringSet.add k (vars e1)
  | If (e1, e2, e3) ->
      union_many [vars e1; vars e2; vars e3]
  | Fun (x, e1) -> StringSet.add x (vars e1)
  | Fix (f, x, e1) -> StringSet.add f (StringSet.add x (vars e1))
  | Cons (e1, e2) -> union_many [vars e1; vars e2]
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      StringSet.add y (StringSet.add ys (union_many [vars e1; vars e_nil; vars e_cons]))
  | SpecialFunc (_, args) -> union_many (List.map vars args)
  | Cdf (d, e1) -> StringSet.union (vars_sample d) (vars e1)

and vars_sample = function
  | Distr1 (_, e1) -> vars e1
  | Distr2 (_, e1, e2) -> StringSet.union (vars e1) (vars e2)

let rec free_vars (ExprNode e) =
  match e with
  | Var x -> StringSet.singleton x
  | Const _ | BoolConst _ | FinConst _ | Nil | Unit | RuntimeError _ ->
      StringSet.empty
  | Let (x, e1, e2) ->
      StringSet.union (free_vars e1) (StringSet.remove x (free_vars e2))
  | Sample d -> free_vars_sample d
  | DiscreteCase cases ->
      union_many
        (List.map
           (fun (b, p) -> StringSet.union (free_vars b) (free_vars p))
           cases)
  | Cmp (_, e1, e2, _) | And (e1, e2) | Or (e1, e2)
  | Pair (e1, e2) | FuncApp (e1, e2)
  | FinEq (e1, e2, _) | Assign (e1, e2) | Seq (e1, e2)
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2)
  | CdfExpr (e1, e2) ->
      StringSet.union (free_vars e1) (free_vars e2)
  | FinCmp (_, e1, e2, _, _) ->
      StringSet.union (free_vars e1) (free_vars e2)
  | Not e1 | First e1 | Second e1 | Observe e1 | Ref e1 | Deref e1 ->
      free_vars e1
  | Reset e1 -> free_vars e1
  | Shift (k, e1) -> StringSet.remove k (free_vars e1)
  | If (e1, e2, e3) ->
      union_many [free_vars e1; free_vars e2; free_vars e3]
  | Fun (x, e1) -> StringSet.remove x (free_vars e1)
  | Fix (f, x, e1) -> remove_many_set [f; x] (free_vars e1)
  | Cons (e1, e2) -> StringSet.union (free_vars e1) (free_vars e2)
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      union_many
        [ free_vars e1
        ; free_vars e_nil
        ; remove_many_set [y; ys] (free_vars e_cons) ]
  | SpecialFunc (_, args) -> union_many (List.map free_vars args)
  | Cdf (d, e1) -> StringSet.union (free_vars_sample d) (free_vars e1)

and free_vars_sample = function
  | Distr1 (_, e1) -> free_vars e1
  | Distr2 (_, e1, e2) -> StringSet.union (free_vars e1) (free_vars e2)

let fresh_avoiding base avoid =
  let rec loop () =
    let x = Util.fresh_var (base ^ "_") in
    if StringSet.mem x avoid then loop () else x
  in
  loop ()

let fresh_var_expr base avoid =
  let x = fresh_avoiding base avoid in
  (x, node (Var x))

let rec subst_var name replacement e =
  subst_var_with name replacement (free_vars replacement) e

and alpha_rename binder body avoid =
  let binder' = fresh_avoiding binder avoid in
  (binder', subst_var binder (node (Var binder')) body)

and rename_if_needed binder body target replacement_fv =
  if StringSet.mem binder replacement_fv then
    let avoid =
      union_many
        [ replacement_fv
        ; vars body
        ; StringSet.singleton target ]
    in
    alpha_rename binder body avoid
  else
    (binder, body)

and subst_var_with name replacement replacement_fv (ExprNode e) =
  match e with
  | Var x when x = name -> replacement
  | Var x -> node (Var x)
  | Const f -> node (Const f)
  | BoolConst b -> node (BoolConst b)
  | Let (x, e1, e2) ->
      let e1' = subst_var_with name replacement replacement_fv e1 in
      if x = name then
        node (Let (x, e1', e2))
      else
        let x', e2' = rename_if_needed x e2 name replacement_fv in
        node (Let (x', e1', subst_var_with name replacement replacement_fv e2'))
  | Sample d -> node (Sample (subst_sample name replacement replacement_fv d))
  | DiscreteCase cases ->
      node
        (DiscreteCase
           (List.map
              (fun (b, p) ->
                 ( subst_var_with name replacement replacement_fv b
                 , subst_var_with name replacement replacement_fv p ))
              cases))
  | Cmp (op, e1, e2, flipped) ->
      node
        (Cmp
           ( op
           , subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2
           , flipped ))
  | And (e1, e2) ->
      node
        (And
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Or (e1, e2) ->
      node
        (Or
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Not e1 -> node (Not (subst_var_with name replacement replacement_fv e1))
  | If (e1, e2, e3) ->
      node
        (If
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2
           , subst_var_with name replacement replacement_fv e3 ))
  | Pair (e1, e2) ->
      node
        (Pair
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | First e1 -> node (First (subst_var_with name replacement replacement_fv e1))
  | Second e1 -> node (Second (subst_var_with name replacement replacement_fv e1))
  | Fun (x, e1) ->
      if x = name then
        node (Fun (x, e1))
      else
        let x', e1' = rename_if_needed x e1 name replacement_fv in
        node (Fun (x', subst_var_with name replacement replacement_fv e1'))
  | FuncApp (e1, e2) ->
      node
        (FuncApp
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | FinConst (k, n) -> node (FinConst (k, n))
  | FinCmp (op, e1, e2, n, flipped) ->
      node
        (FinCmp
           ( op
           , subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2
           , n
           , flipped ))
  | FinEq (e1, e2, n) ->
      node
        (FinEq
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2
           , n ))
  | Observe e1 -> node (Observe (subst_var_with name replacement replacement_fv e1))
  | Fix (f, x, e1) ->
      if f = name || x = name then
        node (Fix (f, x, e1))
      else
        let f', e1' = rename_if_needed f e1 name replacement_fv in
        let x', e1'' = rename_if_needed x e1' name replacement_fv in
        node (Fix (f', x', subst_var_with name replacement replacement_fv e1''))
  | Nil -> node Nil
  | Cons (e1, e2) ->
      node
        (Cons
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      let e1' = subst_var_with name replacement replacement_fv e1 in
      let e_nil' = subst_var_with name replacement replacement_fv e_nil in
      if y = name || ys = name then
        node (MatchList (e1', e_nil', y, ys, e_cons))
      else
        let y', e_cons' = rename_if_needed y e_cons name replacement_fv in
        let ys', e_cons'' = rename_if_needed ys e_cons' name replacement_fv in
        node
          (MatchList
             ( e1'
             , e_nil'
             , y'
             , ys'
             , subst_var_with name replacement replacement_fv e_cons'' ))
  | Ref e1 -> node (Ref (subst_var_with name replacement replacement_fv e1))
  | Deref e1 -> node (Deref (subst_var_with name replacement replacement_fv e1))
  | Assign (e1, e2) ->
      node
        (Assign
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Seq (e1, e2) ->
      node
        (Seq
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Unit -> node Unit
  | RuntimeError s -> node (RuntimeError s)
  | Reset e1 ->
      node (Reset (subst_var_with name replacement replacement_fv e1))
  | Shift (k, e1) ->
      if k = name then
        node (Shift (k, e1))
      else
        let k', e1' = rename_if_needed k e1 name replacement_fv in
        node (Shift (k', subst_var_with name replacement replacement_fv e1'))
  | Add (e1, e2) ->
      node
        (Add
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Sub (e1, e2) ->
      node
        (Sub
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Mul (e1, e2) ->
      node
        (Mul
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | Div (e1, e2) ->
      node
        (Div
           ( subst_var_with name replacement replacement_fv e1
           , subst_var_with name replacement replacement_fv e2 ))
  | SpecialFunc (func, args) ->
      node (SpecialFunc (func, List.map (subst_var_with name replacement replacement_fv) args))
  | Cdf (d, e1) ->
      node
        (Cdf
           ( subst_sample name replacement replacement_fv d
           , subst_var_with name replacement replacement_fv e1 ))
  | CdfExpr (k, e1) ->
      node
        (CdfExpr
           ( subst_var_with name replacement replacement_fv k
           , subst_var_with name replacement replacement_fv e1 ))

and subst_sample name replacement replacement_fv = function
  | Distr1 (kind, e1) ->
      Distr1 (kind, subst_var_with name replacement replacement_fv e1)
  | Distr2 (kind, e1, e2) ->
      Distr2
        ( kind
        , subst_var_with name replacement replacement_fv e1
        , subst_var_with name replacement replacement_fv e2 )

let subst_two name1 replacement1 name2 replacement2 e =
  let avoid =
    union_many [vars e; vars replacement1; vars replacement2]
  in
  let tmp1, tmp1_expr = fresh_var_expr name1 avoid in
  let tmp2, tmp2_expr =
    fresh_var_expr name2 (StringSet.add tmp1 avoid)
  in
  e
  |> subst_var name1 tmp1_expr
  |> subst_var name2 tmp2_expr
  |> subst_var tmp1 replacement1
  |> subst_var tmp2 replacement2

let rec inlineable = function
  | ExprNode (Var _ | Const _ | BoolConst _ | FinConst _ | Fun _ | Fix _ | Unit | Nil) -> true
  | ExprNode (Pair (a, b)) -> inlineable a && inlineable b
  | ExprNode (Cons (a, b)) -> inlineable a && inlineable b
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
        expr_env env (subst_var x e1' e2)
      else if generated_ad_name x then
        match e1' with
        | ExprNode (Pair _) -> expr_env env (subst_var x e1' e2)
        | _ -> node (Let (x, e1', expr_env (StringMap.remove x env) e2))
      else
        node (Let (x, e1', expr_env (StringMap.remove x env) e2))
  | Sample d -> node (Sample (sample_env env d))
  | DiscreteCase cases ->
      node (DiscreteCase (List.map (fun (b, p) -> (expr_env env b, expr_env env p)) cases))
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
      let e1' = expr_env env e1 in
      let e2' = expr_env env e2 in
      (match e1' with
       | ExprNode (Fun (x, body)) when inlineable e2' ->
           expr_env env (subst_var x e2' body)
       | ExprNode (Fix (f, x, body)) when inlineable e2' ->
           (* One-step beta-reduction of a recursive application:
              substitute the recursive name with the whole [fix]
              term and the formal with the argument.  Recursive
              calls inside [body] become FuncApp(Fix(...), ...) and
              are only reduced on demand at the next application
              site, so this terminates. *)
           let body' =
             body
             |> subst_var f e1'
             |> subst_var x e2'
           in
           expr_env env body'
       | _ -> node (FuncApp (e1', e2')))
  | Fix (f, x, e1) ->
      node (Fix (f, x, expr_env (remove_many [f; x] env) e1))
  | FinConst (k, n) -> node (FinConst (k, n))
  | Observe e1 -> node (Observe (expr_env env e1))
  | Nil -> node Nil
  | Cons (e1, e2) -> node (Cons (expr_env env e1, expr_env env e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      let e1' = expr_env env e1 in
      (match e1' with
       | ExprNode Nil -> expr_env env e_nil
       | ExprNode (Cons (hd, tl)) ->
           let branch = subst_two y hd ys tl e_cons in
           expr_env env branch
       | _ ->
           node (MatchList
             ( e1'
             , expr_env env e_nil
             , y
             , ys
             , expr_env (remove_many [y; ys] env) e_cons )))
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
  | Reset e1 -> node (Reset (expr_env env e1))
  | Shift (k, e1) -> node (Shift (k, expr_env (StringMap.remove k env) e1))
  | Add (e1, e2) -> mk_add (expr_env env e1) (expr_env env e2)
  | Sub (e1, e2) -> mk_sub (expr_env env e1) (expr_env env e2)
  | Mul (e1, e2) -> mk_mul (expr_env env e1) (expr_env env e2)
  | Div (e1, e2) -> mk_div (expr_env env e1) (expr_env env e2)
  | SpecialFunc (name, args) -> mk_special name (List.map (expr_env env) args)
  | Cdf (d, e1) -> node (Cdf (sample_env env d, expr_env env e1))
  | CdfExpr (k, e1) -> node (CdfExpr (expr_env env k, expr_env env e1))

and sample_env env = function
  | Distr1 (kind, e1) -> Distr1 (kind, expr_env env e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, expr_env env e1, expr_env env e2)

(* Walks an AST and replaces free occurrences of a variable, like theta, with a float constant. *)
let subst_float name value e =
  subst_var name (mk_const value) e


(* Tries to bring a polynomial into a canonical form.

It handles arithmetic consisting of:

constants
variables
+
-
*
division by numeric constants

So it can combine like terms and cancel polynomial expressions, e.g.

theta + theta
=> 2 * theta

theta - theta
=> 0

theta * theta + (1 - theta) * (theta + 1)
=> 1

(theta + theta) + ((1 - theta) + (0 - (theta + 1)))
=> 0

*)
module Monomial = struct
  type t = (string * int) list
  let compare = compare
end

module PolyMap = Map.Make(Monomial)

let poly_add_term mono coeff poly =
  if coeff = 0.0 then poly
  else
    let old =
      match PolyMap.find_opt mono poly with
      | Some c -> c
      | None -> 0.0
    in
    let coeff' = old +. coeff in
    if coeff' = 0.0 then PolyMap.remove mono poly
    else PolyMap.add mono coeff' poly

let poly_const c =
  poly_add_term [] c PolyMap.empty

let poly_var x =
  poly_add_term [x, 1] 1.0 PolyMap.empty

let poly_add p q =
  PolyMap.fold poly_add_term p q

let poly_scale c p =
  if c = 0.0 then PolyMap.empty
  else PolyMap.fold (fun mono coeff acc -> poly_add_term mono (c *. coeff) acc) p PolyMap.empty

let poly_sub p q =
  poly_add p (poly_scale (-1.0) q)

let monomial_mul m1 m2 =
  let add_power powers (x, n) =
    let old =
      match StringMap.find_opt x powers with
      | Some n -> n
      | None -> 0
    in
    let n' = old + n in
    if n' = 0 then StringMap.remove x powers
    else StringMap.add x n' powers
  in
  StringMap.bindings
    (List.fold_left add_power
       (List.fold_left add_power StringMap.empty m1)
       m2)

let poly_mul p q =
  PolyMap.fold
    (fun m1 c1 acc ->
       PolyMap.fold
         (fun m2 c2 acc' ->
            poly_add_term (monomial_mul m1 m2) (c1 *. c2) acc')
         q acc)
    p PolyMap.empty

let poly_as_const p =
  match PolyMap.bindings p with
  | [] -> Some 0.0
  | [([], c)] -> Some c
  | _ -> None

let option_map2 f x y =
  match x, y with
  | Some x', Some y' -> Some (f x' y')
  | _ -> None

let rec polynomial_of_expr (ExprNode e) =
  match e with
  | Const c -> Some (poly_const c)
  | Var x -> Some (poly_var x)
  | Add (e1, e2) ->
      option_map2 poly_add (polynomial_of_expr e1) (polynomial_of_expr e2)
  | Sub (e1, e2) ->
      option_map2 poly_sub (polynomial_of_expr e1) (polynomial_of_expr e2)
  | Mul (e1, e2) ->
      option_map2 poly_mul (polynomial_of_expr e1) (polynomial_of_expr e2)
  | Div (e1, e2) ->
      (match polynomial_of_expr e1, polynomial_of_expr e2 with
       | Some p1, Some p2 ->
           (match poly_as_const p2 with
            | Some c when c <> 0.0 -> Some (poly_scale (1.0 /. c) p1)
            | _ -> None)
       | _ -> None)
  | _ -> None

let rec multiply_factors = function
  | [] -> mk_const 1.0
  | [x] -> x
  | x :: xs -> mk_mul x (multiply_factors xs)

let rec repeat_expr n e =
  if n <= 0 then []
  else e :: repeat_expr (n - 1) e

let monomial_to_expr mono =
  let factors =
    List.concat
      (List.map
         (fun (x, n) -> repeat_expr n (node (Var x)))
         mono)
  in
  multiply_factors factors

let term_to_expr coeff mono =
  match mono with
  | [] -> mk_const coeff
  | _ ->
      let mono_expr = monomial_to_expr mono in
      if coeff = 1.0 then mono_expr
      else mk_mul (mk_const coeff) mono_expr

let sum_exprs = function
  | [] -> mk_const 0.0
  | x :: xs -> List.fold_left mk_add x xs

let polynomial_to_expr poly =
  let terms =
    PolyMap.bindings poly
    |> List.map (fun (mono, coeff) -> term_to_expr coeff mono)
  in
  sum_exprs terms

let algebraic e =
  let rec go e =
    let e' = expr e in
    match polynomial_of_expr e' with
    | Some p -> polynomial_to_expr p
    | None ->
        (match e' with
         | ExprNode (Add (e1, e2)) -> mk_add (go e1) (go e2)
         | ExprNode (Sub (e1, e2)) -> mk_sub (go e1) (go e2)
         | ExprNode (Mul (e1, e2)) -> mk_mul (go e1) (go e2)
         | ExprNode (Div (e1, e2)) -> mk_div (go e1) (go e2)
         | ExprNode (Pair (e1, e2)) -> mk_pair (go e1) (go e2)
         | ExprNode (First e1) -> mk_first (go e1)
         | ExprNode (Second e1) -> mk_second (go e1)
         | ExprNode (Let (x, e1, e2)) -> expr (node (Let (x, go e1, go e2)))
         | ExprNode (If (e1, e2, e3)) -> expr (node (If (go e1, go e2, go e3)))
         | ExprNode (And (e1, e2)) -> expr (node (And (go e1, go e2)))
         | ExprNode (Or (e1, e2)) -> expr (node (Or (go e1, go e2)))
         | ExprNode (Not e1) -> expr (node (Not (go e1)))
         | ExprNode (Cmp (op, e1, e2, flipped)) ->
             expr (node (Cmp (op, go e1, go e2, flipped)))
         | ExprNode (FinCmp (op, e1, e2, n, flipped)) ->
             expr (node (FinCmp (op, go e1, go e2, n, flipped)))
         | ExprNode (FinEq (e1, e2, n)) ->
             expr (node (FinEq (go e1, go e2, n)))
         | ExprNode (Fun (x, e1)) -> node (Fun (x, go e1))
         | ExprNode (FuncApp (e1, e2)) -> expr (node (FuncApp (go e1, go e2)))
         | ExprNode (Fix (f, x, e1)) -> expr (node (Fix (f, x, go e1)))
         | ExprNode (Observe e1) -> node (Observe (go e1))
         | ExprNode (Cons (e1, e2)) -> node (Cons (go e1, go e2))
         | ExprNode (MatchList (e1, e_nil, y, ys, e_cons)) ->
             expr (node (MatchList (go e1, go e_nil, y, ys, go e_cons)))
         | ExprNode (Ref e1) -> node (Ref (go e1))
         | ExprNode (Deref e1) -> node (Deref (go e1))
         | ExprNode (Assign (e1, e2)) -> node (Assign (go e1, go e2))
         | ExprNode (Seq (e1, e2)) -> expr (node (Seq (go e1, go e2)))
         | ExprNode (Reset e1) -> expr (node (Reset (go e1)))
         | ExprNode (Shift (k, e1)) -> expr (node (Shift (k, go e1)))
         | ExprNode (DiscreteCase cases) ->
             node (DiscreteCase (List.map (fun (b, p) -> (go b, go p)) cases))
         | ExprNode (SpecialFunc (name, args)) ->
             mk_special name (List.map go args)
         | ExprNode (Cdf (d, e1)) -> node (Cdf (go_sample d, go e1))
         | ExprNode (CdfExpr (k, e1)) -> node (CdfExpr (go k, go e1))
         | ExprNode (Sample d) -> node (Sample (go_sample d))
         | _ -> e')
  and go_sample = function
    | Distr1 (kind, e1) -> Distr1 (kind, go e1)
    | Distr2 (kind, e1, e2) -> Distr2 (kind, go e1, go e2)
  in
  go e

(** Symbolic evaluation of deterministic administrative programs.

    Unlike [expr] and [algebraic], this pass evaluates nontrivial let-bound
    values through an environment.  It therefore removes administrative
    lets, pairs, projections, references, and control operators without first
    requiring their right-hand sides to be syntactically inlineable.  Free
    variables are residualized as symbolic expressions.

    Evaluation is best-effort.  Programs that require choosing an unknown
    symbolic branch, contain residual probabilistic operations, or otherwise
    cannot be evaluated are reported as [None] by [evaluate_symbolically]. *)

exception Cannot_symbolically_evaluate of string

type symbolic_value =
  | SExpr of expr
  | SPair of symbolic_value * symbolic_value
  | SClosure of string * expr * symbolic_env
  | SRecClosure of string * string * expr * symbolic_env
  | SRef of symbolic_value ref
  | SCont of (symbolic_value -> symbolic_value)
  | SUnit
  | SNil
  | SCons of symbolic_value * symbolic_value
and symbolic_env = (string * symbolic_value) list

let rec symbolic_lookup name = function
  | [] -> SExpr (node (Var name))
  | (bound_name, value) :: rest ->
      if name = bound_name then value else symbolic_lookup name rest

let rec symbolic_expr = function
  | SExpr expression -> expression
  | SPair (left, right) -> mk_pair (symbolic_expr left) (symbolic_expr right)
  | SRef reference -> node (Ref (symbolic_expr !reference))
  | SUnit -> node Unit
  | SNil -> node Nil
  | SCons (head, tail) -> node (Cons (symbolic_expr head, symbolic_expr tail))
  | SClosure (argument, body, []) -> node (Fun (argument, body))
  | SClosure _ ->
      raise
        (Cannot_symbolically_evaluate
           "cannot reify closure with captured environment")
  | SRecClosure (function_name, argument, body, []) ->
      node (Fix (function_name, argument, body))
  | SRecClosure _ ->
      raise
        (Cannot_symbolically_evaluate
           "cannot reify recursive closure with captured environment")
  | SCont _ ->
      raise
        (Cannot_symbolically_evaluate "cannot reify captured continuation")

let symbolic_bool = function
  | SExpr (ExprNode (BoolConst value)) -> Some value
  | _ -> None

let symbolic_arithmetic operation left right =
  SExpr (operation (symbolic_expr left) (symbolic_expr right))

let rec symbolic_sample environment = function
  | Distr1 (kind, argument) ->
      Distr1 (kind, symbolic_expr (symbolic_eval environment argument))
  | Distr2 (kind, left, right) ->
      Distr2
        ( kind
        , symbolic_expr (symbolic_eval environment left)
        , symbolic_expr (symbolic_eval environment right) )

and symbolic_eval environment expression =
  symbolic_eval_cps environment expression (fun value -> value)

and symbolic_eval_cps environment (ExprNode expression) continuation =
  match expression with
  | Const value -> continuation (SExpr (mk_const value))
  | BoolConst value -> continuation (SExpr (mk_bool value))
  | Var name -> continuation (symbolic_lookup name environment)
  | Let (name, bound, body) ->
      symbolic_eval_cps environment bound (fun value ->
        symbolic_eval_cps ((name, value) :: environment) body continuation)
  | Pair (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation (SPair (left_value, right_value))))
  | First value ->
      symbolic_eval_cps environment value (function
        | SPair (left, _) -> continuation left
        | symbolic ->
            continuation (SExpr (mk_first (symbolic_expr symbolic))))
  | Second value ->
      symbolic_eval_cps environment value (function
        | SPair (_, right) -> continuation right
        | symbolic ->
            continuation (SExpr (mk_second (symbolic_expr symbolic))))
  | Ref value ->
      symbolic_eval_cps environment value (fun symbolic ->
        continuation (SRef (ref symbolic)))
  | Deref value ->
      symbolic_eval_cps environment value (function
        | SRef reference -> continuation !reference
        | symbolic ->
            continuation (SExpr (node (Deref (symbolic_expr symbolic)))))
  | Assign (target, value) ->
      symbolic_eval_cps environment target (fun target_value ->
        symbolic_eval_cps environment value (fun assigned_value ->
          match target_value with
          | SRef reference ->
              reference := assigned_value;
              continuation SUnit
          | _ ->
              raise
                (Cannot_symbolically_evaluate
                   "assignment target is not a reference")))
  | Seq (first, second) ->
      symbolic_eval_cps environment first (fun _ ->
        symbolic_eval_cps environment second continuation)
  | Add (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (symbolic_arithmetic mk_add left_value right_value)))
  | Sub (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (symbolic_arithmetic mk_sub left_value right_value)))
  | Mul (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (symbolic_arithmetic mk_mul left_value right_value)))
  | Div (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (symbolic_arithmetic mk_div left_value right_value)))
  | SpecialFunc (name, arguments) ->
      let rec evaluate_arguments evaluated = function
        | [] ->
            continuation
              (SExpr
                 (mk_special name (List.rev_map symbolic_expr evaluated)))
        | argument :: rest ->
            symbolic_eval_cps environment argument (fun value ->
              evaluate_arguments (value :: evaluated) rest)
      in
      evaluate_arguments [] arguments
  | Cmp (operation, left, right, flipped) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (SExpr
               (expr
                  (node
                     (Cmp
                        ( operation
                        , symbolic_expr left_value
                        , symbolic_expr right_value
                        , flipped )))))))
  | FinCmp (operation, left, right, modulus, flipped) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (SExpr
               (expr
                  (node
                     (FinCmp
                        ( operation
                        , symbolic_expr left_value
                        , symbolic_expr right_value
                        , modulus
                        , flipped )))))))
  | FinEq (left, right, modulus) ->
      symbolic_eval_cps environment left (fun left_value ->
        symbolic_eval_cps environment right (fun right_value ->
          continuation
            (SExpr
               (expr
                  (node
                     (FinEq
                        ( symbolic_expr left_value
                        , symbolic_expr right_value
                        , modulus )))))))
  | And (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        match symbolic_bool left_value with
        | Some false -> continuation (SExpr (mk_bool false))
        | Some true -> symbolic_eval_cps environment right continuation
        | None ->
            symbolic_eval_cps environment right (fun right_value ->
              continuation
                (SExpr
                   (node
                      (And
                         (symbolic_expr left_value, symbolic_expr right_value))))))
  | Or (left, right) ->
      symbolic_eval_cps environment left (fun left_value ->
        match symbolic_bool left_value with
        | Some true -> continuation (SExpr (mk_bool true))
        | Some false -> symbolic_eval_cps environment right continuation
        | None ->
            symbolic_eval_cps environment right (fun right_value ->
              continuation
                (SExpr
                   (node
                      (Or
                         (symbolic_expr left_value, symbolic_expr right_value))))))
  | Not value ->
      symbolic_eval_cps environment value (fun symbolic ->
        match symbolic_bool symbolic with
        | Some value -> continuation (SExpr (mk_bool (not value)))
        | None -> continuation (SExpr (node (Not (symbolic_expr symbolic)))))
  | If (condition, if_true, if_false) ->
      symbolic_eval_cps environment condition (fun condition_value ->
        match symbolic_bool condition_value with
        | Some true ->
            symbolic_eval_cps environment if_true continuation
        | Some false ->
            symbolic_eval_cps environment if_false continuation
        | None ->
            raise
              (Cannot_symbolically_evaluate
                 "cannot choose a branch for a symbolic conditional"))
  | Fun (argument, body) ->
      continuation (SClosure (argument, body, environment))
  | FuncApp (function_expression, argument) ->
      symbolic_eval_cps environment function_expression (fun function_value ->
        symbolic_eval_cps environment argument (fun argument_value ->
          match function_value with
          | SClosure (name, body, captured_environment) ->
              symbolic_eval_cps
                ((name, argument_value) :: captured_environment)
                body continuation
          | SRecClosure
              (function_name, name, body, captured_environment) ->
              symbolic_eval_cps
                ((name, argument_value)
                 :: (function_name, function_value)
                 :: captured_environment)
                body continuation
          | SCont captured -> continuation (captured argument_value)
          | _ ->
              continuation
                (SExpr
                   (node
                      (FuncApp
                         ( symbolic_expr function_value
                         , symbolic_expr argument_value ))))))
  | Fix (function_name, argument, body) ->
      continuation
        (SRecClosure (function_name, argument, body, environment))
  | FinConst (value, modulus) ->
      continuation (SExpr (node (FinConst (value, modulus))))
  | Observe observed ->
      symbolic_eval_cps environment observed (fun value ->
        match symbolic_bool value with
        | Some true -> continuation SUnit
        | Some false ->
            raise (Cannot_symbolically_evaluate "observe failed")
        | None ->
            raise (Cannot_symbolically_evaluate "symbolic observe"))
  | Nil -> continuation SNil
  | Cons (head, tail) ->
      symbolic_eval_cps environment head (fun head_value ->
        symbolic_eval_cps environment tail (fun tail_value ->
          continuation (SCons (head_value, tail_value))))
  | MatchList (value, if_nil, head_name, tail_name, if_cons) ->
      symbolic_eval_cps environment value (function
        | SNil -> symbolic_eval_cps environment if_nil continuation
        | SCons (head, tail) ->
            symbolic_eval_cps
              ((head_name, head) :: (tail_name, tail) :: environment)
              if_cons continuation
        | _ ->
            raise
              (Cannot_symbolically_evaluate "symbolic list match"))
  | Unit -> continuation SUnit
  | RuntimeError message -> raise (Cannot_symbolically_evaluate message)
  | Reset body ->
      let value = symbolic_eval_cps environment body (fun value -> value) in
      continuation value
  | Shift (continuation_name, body) ->
      symbolic_eval_cps
        ((continuation_name, SCont continuation) :: environment)
        body (fun value -> value)
  | Cdf (distribution, point) ->
      symbolic_eval_cps environment point (fun point_value ->
        continuation
          (SExpr
             (node
                (Cdf
                   ( symbolic_sample environment distribution
                   , symbolic_expr point_value )))))
  | CdfExpr (kernel, point) ->
      symbolic_eval_cps environment kernel (fun kernel_value ->
        symbolic_eval_cps environment point (fun point_value ->
          continuation
            (SExpr
               (node
                  (CdfExpr
                     ( symbolic_expr kernel_value
                     , symbolic_expr point_value ))))))
  | Sample _ -> raise (Cannot_symbolically_evaluate "sample")
  | DiscreteCase _ ->
      raise (Cannot_symbolically_evaluate "discrete case")

let evaluate_symbolically expression =
  try Some (algebraic (symbolic_expr (symbolic_eval [] expression))) with
  | Cannot_symbolically_evaluate _ -> None

let evaluate_symbolically_or_original expression =
  match evaluate_symbolically expression with
  | Some evaluated -> evaluated
  | None -> expression
