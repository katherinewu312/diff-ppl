(* ADEV-style forward-mode AD for already-discretized Slice programs.

   Deterministic terms are transformed using ordinary dual numbers,
   represented in the existing AST as pairs [(primal, tangent)].
   Finite and boolean values have no tangent component.

   Discrete distributions are handled by exact enumeration in
   continuation-passing style:

     Dexpect[discrete(p_i : v_i)] k
       = sum_i D[p_i] *D Dexpect[v_i] k

   This is the n-ary analogue of ADEV's flip_enum rule. *)

open Ast

module StringSet = Set.Make(String)

type env =
  { param : string
  ; bound : StringSet.t
  }

let empty_env param = { param; bound = StringSet.empty }
let extend env x = { env with bound = StringSet.add x env.bound }
let is_bound env x = StringSet.mem x env.bound

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

let is_float_ty ty =
  match Ast.force ty with
  | TFloat _ -> true
  | _ -> false

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

and primal env ((ty, _) as te) =
  if is_float_ty ty then dual_primal (det_ad env te)
  else det_ad env te

and det_ad env (ty, TAExprNode ae) =
  match ae with
  | Const f -> dual_const f
  | BoolConst b -> bool b
  | Var x ->
      if is_float_ty ty then
        if is_bound env x then node (Var x)
        else dual_seed x (if x = env.param then 1.0 else 0.0)
      else
        node (Var x)

  | Add (e1, e2) -> dual_add (det_ad env e1) (det_ad env e2)
  | Sub (e1, e2) -> dual_sub (det_ad env e1) (det_ad env e2)
  | Mul (e1, e2) -> dual_mul (det_ad env e1) (det_ad env e2)
  | Div (e1, e2) -> dual_div (det_ad env e1) (det_ad env e2)

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
      node (Fun (x, det_ad (extend env x) e1))
  | FuncApp (e1, e2) ->
      node (FuncApp (det_ad env e1, det_ad env e2))
  | LoopApp (e1, e2, n) ->
      node (LoopApp (det_ad env e1, det_ad env e2, n))
  | Fix (f, x, e1) ->
      node (Fix (f, x, det_ad (extend (extend env f) x) e1))

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
      Cdf_ad.cdf_expr (det_ad env kernel) (det_ad env point)
  | SpecialFunc (name, args) ->
      let dargs = List.map (det_ad env) args in
      let primal_args = List.map dual_primal dargs in
      if is_float_ty ty then
        pair
          (node (SpecialFunc (name, primal_args)))
          (runtime_error ("differentiation of special function " ^ name ^ " is not implemented"))
      else
        node (SpecialFunc (name, primal_args))

  | RuntimeError msg ->
      if is_float_ty ty then dual_runtime msg else node (RuntimeError msg)
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before ADEV"
  | DistrCase _ ->
      unsupported "discrete distribution appeared in deterministic AD position"

and trans env ((_, TAExprNode ae) as te) k =
  match ae with
  | DistrCase cases ->
      let terms =
        List.map
          (fun (branch, prob) ->
             dual_mul (det_ad env prob) (trans env branch k))
          cases
      in
      sum_duals terms

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

  | Add (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (dual_add d1 d2)))
  | Sub (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (dual_sub d1 d2)))
  | Mul (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (dual_mul d1 d2)))
  | Div (e1, e2) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (dual_div d1 d2)))

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
        trans env e2 (fun d2 -> k (node (FuncApp (d1, d2)))))
  | LoopApp (e1, e2, n) ->
      trans env e1 (fun d1 ->
        trans env e2 (fun d2 -> k (node (LoopApp (d1, d2, n)))))

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

  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before ADEV"

(* discretized program
-> raw AD dual program
-> Simplify.expr raw_program
-> simplied AD dual program *)

let dual_expectation_raw ?(param = "theta") te =
  let ty, _ = te in
  trans (empty_env param) te (objective_dual ty)

let gradient_raw ?(param = "theta") te =
  dual_tangent (dual_expectation_raw ~param te)

let dual_expectation ?(param = "theta") te =
  Simplify.expr (dual_expectation_raw ~param te)

let gradient ?(param = "theta") te =
  Simplify.expr (gradient_raw ~param te)
