(* ADEV-style forward-mode AD for already-discretized Slice programs.

   Deterministic terms are transformed using ordinary dual numbers,
   represented in the existing AST as pairs [(primal, tangent)].
   Finite and boolean values have no tangent component.

   Discrete distributions are handled by exact enumeration in
   continuation-passing style:

     Dexpect[discrete(p_i : v_i)] k
       = sum_i let phat_i = D[p_i] in
               let bhat_i = Dexpect[v_i] k in
               phat_i *D bhat_i

   This is the n-ary analog of ADEV's flip_enum rule. *)

open Ast

module StringSet = Util.StringSet
module StringMap = Map.Make(String)

type seeds = float StringMap.t

type env =
  { seeds : seeds (* free parameters to differentiate with respect to *)
  ; bound : StringSet.t (* local program variables that should not be treated as seed parameters *)
  }

let no_seeds = StringMap.empty
let add_seed = StringMap.add
let seeds_of_param param = StringMap.singleton param 1.0
let empty_env seeds = { seeds; bound = StringSet.empty }
let extend env x = { env with bound = StringSet.add x env.bound }
let seed_of env x =
  match StringMap.find_opt x env.seeds with
  | Some seed -> seed
  | None -> 0.0

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
let runtime_error msg = node (RuntimeError ("ADEV: " ^ msg))

let unsupported msg = failwith ("ADEV: " ^ msg)

let bind_ad hint rhs body =
  let x = Util.fresh_var hint in
  node (Let (x, rhs, body (node (Var x))))

let dual_primal e =
  match e with
  | ExprNode (Pair (p, _)) -> p
  | _ -> first e

let dual_tangent e =
  match e with
  | ExprNode (Pair (_, t)) -> t
  | _ -> second e

let dual_const f = pair (const f) (const 0.0)
let dual_seed x tangent = pair (node (Var x)) (const tangent)
let dual_runtime msg = pair (runtime_error msg) (runtime_error msg)

let dual_add a b =
  let ap = dual_primal a and at = dual_tangent a in
  let bp = dual_primal b and bt = dual_tangent b in
  pair (add ap bp) (add at bt)

let dual_sub a b =
  let ap = dual_primal a and at = dual_tangent a in
  let bp = dual_primal b and bt = dual_tangent b in
  pair (sub ap bp) (sub at bt)

let dual_mul a b =
  let ap = dual_primal a and at = dual_tangent a in
  let bp = dual_primal b and bt = dual_tangent b in
  pair (mul ap bp) (add (mul ap bt) (mul at bp))

let dual_div a b =
  let ap = dual_primal a and at = dual_tangent a in
  let bp = dual_primal b and bt = dual_tangent b in
  pair
    (div ap bp)
    (div (sub (mul at bp) (mul ap bt)) (mul bp bp))

let rec sum_duals = function
  | [] -> pair (const 0.0) (const 0.0)
  | [x] -> x
  | x :: xs -> dual_add x (sum_duals xs)

let dual_binary op e1 e2 =
  bind_ad "_adev_yhat" e1 (fun yhat1 ->
    bind_ad "_adev_yhat" e2 (fun yhat2 ->
      op yhat1 yhat2))

let effect_of (_, eff, _) = Ast.force_effect eff
let is_prob_effect eff =
  match Ast.force_effect eff with
  | Prob -> true
  | Pure | EMeta _ -> false

let function_returns_prob (ty, _, _) =
  match Ast.force ty with
  | TFun (_, eff, _) -> is_prob_effect eff
  | _ -> false

let rec texpr_contains_sample (_, _, TAExprNode ae) =
  match ae with
  | Sample _ -> true
  | Const _ | Var _ | BoolConst _ | Nil | Unit
  | FinConst _ | RuntimeError _ -> false
  | Let (_, e1, e2) | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2)
  | Div (e1, e2) | Cmp (_, e1, e2, _) | FinCmp (_, e1, e2, _, _)
  | FinEq (e1, e2, _) | And (e1, e2) | Or (e1, e2) | Pair (e1, e2)
  | FuncApp (e1, e2) | Cons (e1, e2) | Assign (e1, e2) | Seq (e1, e2)
  | CdfExpr (e1, e2) ->
      texpr_contains_sample e1 || texpr_contains_sample e2
  | Cdf (dist, point) ->
      sample_contains_sample dist || texpr_contains_sample point
  | Not e1 | First e1 | Second e1 | Observe e1 | Ref e1 | Deref e1 ->
      texpr_contains_sample e1
  | Reset e1 -> texpr_contains_sample e1
  | Shift (_, e1) -> texpr_contains_sample e1
  | If (e1, e2, e3) ->
      texpr_contains_sample e1 || texpr_contains_sample e2 || texpr_contains_sample e3
  | Fun (_, e1) | Fix (_, _, e1) -> texpr_contains_sample e1
  | MatchList (e1, e2, _, _, e3) ->
      texpr_contains_sample e1 || texpr_contains_sample e2 || texpr_contains_sample e3
  | DiscreteCase cases ->
      List.exists
        (fun (branch, prob) ->
           texpr_contains_sample branch || texpr_contains_sample prob)
        cases
  | SpecialFunc (_, args) -> List.exists texpr_contains_sample args

and sample_contains_sample = function
  | Distr1 (_, e1) -> texpr_contains_sample e1
  | Distr2 (_, e1, e2) -> texpr_contains_sample e1 || texpr_contains_sample e2

let objective_dual ty dvalue =
  match Ast.force ty with
  | TFloat _ -> dvalue
  | TBool ->
      pair
        (node (If (dvalue, const 1.0, const 0.0)))
        (const 0.0)
  | _ ->
      unsupported "top-level AD objective must be float- or bool-valued"

let rec sample_dual env = function
  | Distr1 (kind, e1) -> Distr1 (kind, det_ad env e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, det_ad env e1, det_ad env e2)

and cdf_kernel_dual env ((_, _, TAExprNode ae) as te) =
  match ae with
  | Sample dist -> node (Sample (sample_dual env dist))
  | Add (e1, e2) when texpr_contains_sample te ->
      node (Add (cdf_kernel_dual env e1, cdf_kernel_dual env e2))
  | Sub (e1, e2) when texpr_contains_sample te ->
      node (Sub (cdf_kernel_dual env e1, cdf_kernel_dual env e2))
  | Mul (e1, e2) when texpr_contains_sample te ->
      node (Mul (cdf_kernel_dual env e1, cdf_kernel_dual env e2))
  | Div (e1, e2) when texpr_contains_sample te ->
      node (Div (cdf_kernel_dual env e1, cdf_kernel_dual env e2))
  | _ -> det_ad env te

and primal env ((ty, _, _) as te) =
  if Util.is_float_ty ty then dual_primal (det_ad env te)
  else det_ad env te

and det_binary env op e1 e2 =
  dual_binary op (det_ad env e1) (det_ad env e2)

and prob_cps_body env body =
  let k = Util.fresh_var "_adev_k" in
  node
    (Fun
       ( k
       , trans env body
           (fun v -> node (FuncApp (node (Var k), v))) ))

and det_ad env (ty, eff, TAExprNode ae) =
  match ae with
  | Const f -> dual_const f
  | BoolConst b -> bool b
  | Var x ->
      if Util.is_float_ty ty then
        if StringSet.mem x env.bound then node (Var x)
        else dual_seed x (seed_of env x)
      else
        node (Var x)

  | Add (e1, e2) -> det_binary env dual_add e1 e2
  | Sub (e1, e2) -> det_binary env dual_sub e1 e2
  | Mul (e1, e2) -> det_binary env dual_mul e1 e2
  | Div (e1, e2) -> det_binary env dual_div e1 e2

  | Cmp (op, e1, e2, flipped) ->
      node (Cmp (op, primal env e1, primal env e2, flipped))
  | FinCmp (op, e1, e2, n, flipped) ->
      node (FinCmp (op, det_ad env e1, det_ad env e2, n, flipped))
  | FinEq (e1, e2, n) ->
      node (FinEq (det_ad env e1, det_ad env e2, n))
  | And (e1, e2) -> node (If (det_ad env e1, det_ad env e2, bool false))
  | Or (e1, e2) -> node (If (det_ad env e1, bool true, det_ad env e2))
  | Not e1 -> node (Not (det_ad env e1))
  | If (e1, e2, e3) ->
      node (If (det_ad env e1, det_ad env e2, det_ad env e3))

  | Let (x, e1, e2) ->
      let e1' = det_ad env e1 in
      node (Let (x, e1', det_ad (extend env x) e2))

  | Pair (e1, e2) -> pair (det_ad env e1) (det_ad env e2)
  | First e1 -> first (det_ad env e1)
  | Second e1 -> second (det_ad env e1)

  | Fun (x, e1) ->
      if is_prob_effect (effect_of e1) then
        node (Fun (x, prob_cps_body (extend env x) e1))
      else
        node (Fun (x, det_ad (extend env x) e1))
  | FuncApp (e1, e2) ->
      if is_prob_effect eff then
        unsupported "probabilistic function application appeared in deterministic AD position"
      else
        node (FuncApp (det_ad env e1, det_ad env e2))
  | Fix (f, x, e1) ->
      let env' = extend (extend env f) x in
      if is_prob_effect (effect_of e1) then
        node (Fix (f, x, prob_cps_body env' e1))
      else
        node (Fix (f, x, det_ad env' e1))

  | FinConst (k, n) -> node (FinConst (k, n))
  | Observe e1 -> node (Observe (det_ad env e1))
  | Nil -> node Nil
  | Cons (e1, e2) -> node (Cons (det_ad env e1, det_ad env e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      node (MatchList
        ( det_ad env e1
        , det_ad env e_nil
        , y
        , ys
        , det_ad (extend (extend env y) ys) e_cons ))
  | Ref e1 -> node (Ref (det_ad env e1))
  | Deref e1 -> node (Deref (det_ad env e1))
  | Assign (e1, e2) -> node (Assign (det_ad env e1, det_ad env e2))
  | Seq (e1, e2) -> node (Seq (det_ad env e1, det_ad env e2))
  | Unit -> unit_

  | Cdf (dist_exp, point) ->
      Cdf_ad.cdf (sample_dual env dist_exp) (det_ad env point)
  | CdfExpr (kernel, point) ->
      Cdf_ad.cdf_expr (cdf_kernel_dual env kernel) (det_ad env point)
  | SpecialFunc (name, args) ->
      let dargs = List.map (det_ad env) args in
      let primal_args = List.map dual_primal dargs in
      let primal = Simplify.mk_special name primal_args in
      if Util.is_float_ty ty then
        (match name, dargs with
         | "sqrt", [darg] ->
             pair
               primal
               (div (dual_tangent darg) (mul (const 2.0) primal))
         | _ ->
             pair
               primal
               (runtime_error ("differentiation of special function " ^ name ^ " is not implemented")))
      else
        primal

  | RuntimeError msg ->
      if Util.is_float_ty ty then dual_runtime msg else node (RuntimeError msg)
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before ADEV"
  | DiscreteCase _ ->
      unsupported "discrete distribution appeared in deterministic AD position"

and trans_binary env op e1 e2 k =
  trans env e1 (fun d1 ->
    trans env e2 (fun d2 -> k (op d1 d2)))

and trans env ((_, _, TAExprNode ae) as te) k =
  match ae with
  | DiscreteCase cases ->
      let rec bind_cases chats = function
        | [] -> sum_duals (List.rev chats)
        | (branch, prob) :: rest ->
            bind_ad "_adev_phat" (det_ad env prob) (fun phat ->
              bind_ad "_adev_bhat" (trans env branch k) (fun bhat ->
                bind_ad "_adev_chat" (dual_mul phat bhat) (fun chat ->
                  bind_cases (chat :: chats) rest)))
      in
      bind_cases [] cases

  | Let (x, e1, e2) ->
      trans env e1 (fun dx ->
        node (Let (x, dx, trans (extend env x) e2 k)))

  | If (e1, e2, e3) ->
      trans env e1 (fun cond ->
        node (If (cond, trans env e2 k, trans env e3 k)))

  | And (e1, e2) ->
      trans env e1 (fun b1 ->
        node (If (b1, trans env e2 k, k (bool false))))

  | Or (e1, e2) ->
      trans env e1 (fun b1 ->
        node (If (b1, k (bool true), trans env e2 k)))

  | Not e1 ->
      trans env e1 (fun b1 -> k (node (Not b1)))

  | Seq (e1, e2) ->
      trans env e1 (fun _ -> trans env e2 k)

  | Observe e1 ->
      trans env e1 (fun b ->
        node (Seq (node (Observe b), k unit_)))

  | Add (e1, e2) -> trans_binary env (dual_binary dual_add) e1 e2 k
  | Sub (e1, e2) -> trans_binary env (dual_binary dual_sub) e1 e2 k
  | Mul (e1, e2) -> trans_binary env (dual_binary dual_mul) e1 e2 k
  | Div (e1, e2) -> trans_binary env (dual_binary dual_div) e1 e2 k

  | Cmp (op, e1, e2, flipped) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 ->
          k (node (Cmp (op, dual_primal d1, dual_primal d2, flipped)))))
  | FinCmp (op, e1, e2, n, flipped) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 ->
          k (node (FinCmp (op, d1, d2, n, flipped)))))
  | FinEq (e1, e2, n) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 ->
          k (node (FinEq (d1, d2, n)))))

  | Pair (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (pair d1 d2)))
  | First e1 ->
      trans env e1 (fun d1 -> k (first d1))
  | Second e1 ->
      trans env e1 (fun d1 -> k (second d1))
  | FuncApp (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 ->
          if function_returns_prob e1 then
            let x = Util.fresh_var "_adev_arg" in
            let cont = node (Fun (x, k (node (Var x)))) in
            node (FuncApp (node (FuncApp (d1, d2)), cont))
          else
            k (node (FuncApp (d1, d2)))))
  | Cons (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (node (Cons (d1, d2)))))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      trans env e1 (fun d_match ->
        node (MatchList
          ( d_match
          , trans env e_nil k
          , y
          , ys
          , trans (extend (extend env y) ys) e_cons k )))

  | Ref e1 ->
      trans env e1 (fun d1 -> k (node (Ref d1)))
  | Deref e1 ->
      trans env e1 (fun d1 -> k (node (Deref d1)))
  | Assign (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (node (Assign (d1, d2)))))

  | Const _ | BoolConst _ | Var _ | Fun _ | Fix _ | FinConst _ | Nil
  | Unit | Cdf _ | CdfExpr _ | SpecialFunc _
  | RuntimeError _ ->
      k (det_ad env te)

  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"

  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before ADEV"

(* discretized program
-> raw AD dual program
-> Simplify.expr raw_program
-> simplied AD dual program *)

let dual_expectation_with_seeds seeds te =
  let ty, _, _ = te in
  trans (empty_env seeds) te (objective_dual ty)

let gradient_with_seeds seeds te =
  dual_tangent (dual_expectation_with_seeds seeds te)

let gradient_vector_raw te =
  Util.free_float_vars te
  |> StringSet.elements
  |> List.map (fun param -> gradient_with_seeds (seeds_of_param param) te)
  |> Util.expr_list

let dual_expectation_vector_raw te =
  match StringSet.elements (Util.free_float_vars te) with
  | [] ->
      let dual = dual_expectation_with_seeds no_seeds te in
      pair (dual_primal dual) (node Nil)
  | param :: params ->
      let first_dual = dual_expectation_with_seeds (seeds_of_param param) te in
      let rest_gradients =
        List.map
          (fun param -> gradient_with_seeds (seeds_of_param param) te)
          params
      in
      pair
        (dual_primal first_dual)
        (Util.expr_list (dual_tangent first_dual :: rest_gradients))

let dual_expectation_raw ?param ?seeds te =
  match seeds, param with
  | Some seeds, _ -> dual_expectation_with_seeds seeds te
  | None, Some param -> dual_expectation_with_seeds (seeds_of_param param) te
  | None, None -> dual_expectation_vector_raw te

let gradient_raw ?param ?seeds te =
  match seeds, param with
  | Some seeds, _ -> gradient_with_seeds seeds te
  | None, Some param -> gradient_with_seeds (seeds_of_param param) te
  | None, None -> gradient_vector_raw te

let dual_expectation ?param ?seeds te =
  Simplify.algebraic (dual_expectation_raw ?param ?seeds te)

let gradient ?param ?seeds te =
  Simplify.algebraic (gradient_raw ?param ?seeds te)
