(* Evaluates / computes the expectation of a program. Specify --expect in diff_ppl. *)

open Ast

module StringSet = Util.StringSet

let node e = ExprNode e
let const = Simplify.mk_const
let bool = Simplify.mk_bool
let unit_ = node Unit
let pair = Simplify.mk_pair
let first = Simplify.mk_first
let second = Simplify.mk_second
let add = Simplify.mk_add
let sub = Simplify.mk_sub
let mul = Simplify.mk_mul
let div = Simplify.mk_div
let special = Simplify.mk_special

let unsupported msg = failwith ("Eval: " ^ msg)

let effect_of (_, eff, _) =
  Ast.force_effect eff

let is_prob_effect eff =
  match Ast.force_effect eff with
  | Prob -> true
  | Pure | EMeta _ -> false

let function_returns_prob (ty, _, _) =
  match Ast.force ty with
  | TFun (_, eff, _) -> is_prob_effect eff
  | _ -> false

let bind_eval hint rhs body =
  let x = Util.fresh_var hint in
  node (Let (x, rhs, body (node (Var x))))

let rec sum_exprs = function
  | [] -> const 0.0
  | [x] -> x
  | x :: xs -> add x (sum_exprs xs)

let top_value ty v =
  match Ast.force ty with
  | TFloat _ -> v
  | TBool -> node (If (v, const 1.0, const 0.0))
  | _ -> unsupported "top-level expectation must be float- or bool-valued"

let rec det_sample env = function
  | Distr1 (kind, e1) -> Distr1 (kind, det env e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, det env e1, det env e2)

and cdf_primal dist point =
  Cdf_derivative.cdf dist point
  |> Cdf_derivative.dual_primal

and cdf_expr_primal kernel point =
  Cdf_derivative.cdf_expr kernel point
  |> Cdf_derivative.dual_primal

and prob_cps_body env body =
  let k = Util.fresh_var "_eval_k" in
  node
    (Fun
       ( k
       , prob_trans env body (fun v -> node (FuncApp (node (Var k), v))) ))

and det env (_ty, eff, TAExprNode ae) =
  match ae with
  | Const f -> const f
  | BoolConst b -> bool b
  | Var x -> node (Var x)
  | Add (e1, e2) -> add (det env e1) (det env e2)
  | Sub (e1, e2) -> sub (det env e1) (det env e2)
  | Mul (e1, e2) -> mul (det env e1) (det env e2)
  | Div (e1, e2) -> div (det env e1) (det env e2)
  | SpecialFunc (name, args) -> special name (List.map (det env) args)
  | Cmp (op, e1, e2, flipped) ->
      node (Cmp (op, det env e1, det env e2, flipped))
  | FinCmp (op, e1, e2, n, flipped) ->
      node (FinCmp (op, det env e1, det env e2, n, flipped))
  | FinEq (e1, e2, n) ->
      node (FinEq (det env e1, det env e2, n))
  | And (e1, e2) -> node (And (det env e1, det env e2))
  | Or (e1, e2) -> node (Or (det env e1, det env e2))
  | Not e1 -> node (Not (det env e1))
  | If (e1, e2, e3) -> node (If (det env e1, det env e2, det env e3))
  | Let (x, e1, e2) ->
      node (Let (x, det env e1, det (StringSet.add x env) e2))
  | Pair (e1, e2) -> pair (det env e1) (det env e2)
  | First e1 -> first (det env e1)
  | Second e1 -> second (det env e1)
  | Fun (x, e1) ->
      let env' = StringSet.add x env in
      if is_prob_effect (effect_of e1) then
        node (Fun (x, prob_cps_body env' e1))
      else
        node (Fun (x, det env' e1))
  | FuncApp (e1, e2) ->
      if is_prob_effect eff then
        unsupported "probabilistic function application appeared in deterministic evaluation position"
      else
        node (FuncApp (det env e1, det env e2))
  | Fix (f, x, e1) ->
      let env' = StringSet.add f (StringSet.add x env) in
      if is_prob_effect (effect_of e1) then
        node (Fix (f, x, prob_cps_body env' e1))
      else
        node (Fix (f, x, det env' e1))
  | FinConst (k, n) -> node (FinConst (k, n))
  | Observe e1 -> node (Observe (det env e1))
  | Nil -> node Nil
  | Cons (e1, e2) -> node (Cons (det env e1, det env e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      node
        (MatchList
           ( det env e1
           , det env e_nil
           , y
           , ys
           , det (StringSet.add y (StringSet.add ys env)) e_cons ))
  | Ref e1 -> node (Ref (det env e1))
  | Deref e1 -> node (Deref (det env e1))
  | Assign (e1, e2) -> node (Assign (det env e1, det env e2))
  | Seq (e1, e2) -> node (Seq (det env e1, det env e2))
  | Unit -> unit_
  | Cdf (dist, point) -> cdf_primal (det_sample env dist) (det env point)
  | CdfExpr (kernel, point) -> cdf_expr_primal (det env kernel) (det env point)
  | RuntimeError msg -> node (RuntimeError msg)
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before Eval"
  | DiscreteCase _ ->
      unsupported "discrete distribution appeared in deterministic evaluation position"

and trans_binary env op e1 e2 k =
  prob_trans env e1 (fun v1 ->
    prob_trans env e2 (fun v2 ->
      bind_eval "_eval_y" (op v1 v2) k))

and trans_args env args k =
  match args with
  | [] -> k []
  | arg :: rest ->
      prob_trans env arg (fun v ->
        trans_args env rest (fun vs -> k (v :: vs)))

and prob_trans env ((_, _, TAExprNode ae) as te) k =
  if not (is_prob_effect (effect_of te)) then
    bind_eval "_eval_y" (det env te) k
  else
    match ae with
    | DiscreteCase cases ->
        let rec bind_cases acc = function
          | [] -> sum_exprs (List.rev acc)
          | (branch, prob) :: rest ->
              bind_eval "_eval_p" (det env prob) (fun p ->
                bind_eval "_eval_b" (prob_trans env branch k) (fun b ->
                  bind_cases (mul p b :: acc) rest))
        in
        bind_cases [] cases
    | Let (x, e1, e2) ->
        if is_prob_effect (effect_of e1) then
          prob_trans env e1 (fun v ->
            node (Let (x, v, prob_trans (StringSet.add x env) e2 k)))
        else
          node (Let (x, det env e1, prob_trans (StringSet.add x env) e2 k))
    | If (e1, e2, e3) ->
        if is_prob_effect (effect_of e1) then
          prob_trans env e1 (fun cond ->
            node (If (cond, prob_trans env e2 k, prob_trans env e3 k)))
        else
          node (If (det env e1, prob_trans env e2 k, prob_trans env e3 k))
    | And (e1, e2) ->
        prob_trans env e1 (fun b1 ->
          node (If (b1, prob_trans env e2 k, k (bool false))))
    | Or (e1, e2) ->
        prob_trans env e1 (fun b1 ->
          node (If (b1, k (bool true), prob_trans env e2 k)))
    | Not e1 ->
        prob_trans env e1 (fun b1 -> k (node (Not b1)))
    | Seq (e1, e2) ->
        if is_prob_effect (effect_of e1) then
          prob_trans env e1 (fun _ -> prob_trans env e2 k)
        else
          node (Seq (det env e1, prob_trans env e2 k))
    | Observe e1 ->
        prob_trans env e1 (fun b -> node (Seq (node (Observe b), k unit_)))
    | Add (e1, e2) -> trans_binary env add e1 e2 k
    | Sub (e1, e2) -> trans_binary env sub e1 e2 k
    | Mul (e1, e2) -> trans_binary env mul e1 e2 k
    | Div (e1, e2) -> trans_binary env div e1 e2 k
    | SpecialFunc (name, args) ->
        trans_args env args (fun args ->
          bind_eval "_eval_y" (special name args) k)
    | Cmp (op, e1, e2, flipped) ->
        prob_trans env e1 (fun v1 ->
          prob_trans env e2 (fun v2 ->
            k (node (Cmp (op, v1, v2, flipped)))))
    | FinCmp (op, e1, e2, n, flipped) ->
        prob_trans env e1 (fun v1 ->
          prob_trans env e2 (fun v2 ->
            k (node (FinCmp (op, v1, v2, n, flipped)))))
    | FinEq (e1, e2, n) ->
        prob_trans env e1 (fun v1 ->
          prob_trans env e2 (fun v2 -> k (node (FinEq (v1, v2, n)))))
    | Pair (e1, e2) ->
        prob_trans env e1 (fun v1 ->
          prob_trans env e2 (fun v2 -> k (pair v1 v2)))
    | First e1 ->
        prob_trans env e1 (fun v -> k (first v))
    | Second e1 ->
        prob_trans env e1 (fun v -> k (second v))
    | FuncApp (e1, e2) ->
        prob_trans env e1 (fun f ->
          prob_trans env e2 (fun arg ->
            if function_returns_prob e1 then
              let x = Util.fresh_var "_eval_arg" in
              let cont = node (Fun (x, k (node (Var x)))) in
              node (FuncApp (node (FuncApp (f, arg)), cont))
            else
              k (node (FuncApp (f, arg)))))
    | Cons (e1, e2) ->
        prob_trans env e1 (fun v1 ->
          prob_trans env e2 (fun v2 -> k (node (Cons (v1, v2)))))
    | MatchList (e1, e_nil, y, ys, e_cons) ->
        prob_trans env e1 (fun v_match ->
          node
            (MatchList
               ( v_match
               , prob_trans env e_nil k
               , y
               , ys
               , prob_trans (StringSet.add y (StringSet.add ys env)) e_cons k )))
    | Ref e1 ->
        prob_trans env e1 (fun v -> k (node (Ref v)))
    | Deref e1 ->
        prob_trans env e1 (fun v -> k (node (Deref v)))
    | Assign (e1, e2) ->
        prob_trans env e1 (fun v1 ->
          prob_trans env e2 (fun v2 -> k (node (Assign (v1, v2)))))
    | Cdf _ | CdfExpr _ ->
        k (det env te)
    | Const _ | BoolConst _ | Var _ | Fun _ | Fix _ | FinConst _ | Nil | Unit
    | RuntimeError _ ->
        k (det env te)
    | Reset _ | Shift _ ->
        unsupported "shift/reset are internal reverse-AD constructs"
    | Sample _ ->
        unsupported "continuous Sample remained in program; run discretization before Eval"

let expectation_raw ((ty, _, _) as te) =
  prob_trans StringSet.empty te (top_value ty)

let deterministic_raw te =
  Discretization.texpr_to_expr te

let raw ((_, eff, _) as te) =
  if is_prob_effect eff then expectation_raw te else deterministic_raw te

let apply_values values e =
  List.fold_left
    (fun acc (name, value) -> Simplify.subst_float name value acc)
    e
    values

let is_closed e =
  Simplify.StringSet.is_empty (Simplify.free_vars e)

let try_eval_closed e =
  let simplified = Simplify.algebraic e in
  if is_closed simplified then
    try Simplify.algebraic (Interp.eval_to_expr [] simplified) with
    | Interp.RuntimeError _ | Interp.ObserveFailure -> simplified
  else
    simplified

let eval ?(values = []) te =
  raw te
  |> apply_values values
  |> try_eval_closed
