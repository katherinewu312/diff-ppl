(* Deterministic reverse-mode AD.

   Float values are represented as [(primal, adjoint_ref)].  The
   transformation is continuation-based: local arithmetic nodes call
   the continuation first, which seeds/propagates adjoints through the
   rest of the program, then perform their local backprop updates.

   Probabilistic constructs are intentionally rejected here; the
   expectation-level reverse rules will be added separately. *)

open Ast

module StringSet = Adev.StringSet

type seeds = Adev.seeds

let no_seeds = Adev.no_seeds
let add_seed = Adev.add_seed
let seeds_of_param = Adev.seeds_of_param

let node e = ExprNode e
let const = Simplify.mk_const
let bool = Simplify.mk_bool
let pair = Simplify.mk_pair
let first = Simplify.mk_first
let second = Simplify.mk_second
let add = Simplify.mk_add
let sub = Simplify.mk_sub
let mul = Simplify.mk_mul
let div = Simplify.mk_div
let special = Simplify.mk_special

let ref_ e = node (Ref e)
let deref e = node (Deref e)
let assign e1 e2 = node (Assign (e1, e2))
let seq e1 e2 = node (Seq (e1, e2))
let unit_ = node Unit
let zero = const 0.0
let one = const 1.0

let unsupported msg = failwith ("Reverse AD: " ^ msg)

let is_float_ty ty =
  match Ast.force ty with
  | TFloat _ -> true
  | _ -> false

let effect_of (_, eff, _) = Ast.force_effect eff

let primal e =
  match e with
  | ExprNode (Pair (p, _)) -> p
  | _ -> first e

let adjoint e =
  match e with
  | ExprNode (Pair (_, a)) -> a
  | _ -> second e

let adjoint_value e = deref (adjoint e)

let reverse_float primal = pair primal (ref_ zero)

let add_to_ref r delta =
  assign r (add (deref r) delta)

let add_adjoint yhat delta =
  add_to_ref (adjoint yhat) delta

let bind_rev hint rhs body =
  let x = Util.fresh_var hint in
  node (Let (x, rhs, body (node (Var x))))

let rec sequence = function
  | [] -> unit_
  | [e] -> e
  | e :: es -> seq e (sequence es)

let binary_reverse primal_op back1 back2 yhat1 yhat2 k =
  bind_rev "_rev_yhat"
    (reverse_float (primal_op (primal yhat1) (primal yhat2)))
    (fun yhat ->
       sequence
         [ k yhat
         ; add_adjoint yhat1 (back1 yhat yhat1 yhat2)
         ; add_adjoint yhat2 (back2 yhat yhat1 yhat2)
         ])

let rec sample_value env = function
  | Distr1 (kind, e1) -> Distr1 (kind, primal (value env e1))
  | Distr2 (kind, e1, e2) ->
      Distr2 (kind, primal (value env e1), primal (value env e2))

and value env (ty, _, TAExprNode ae) =
  match ae with
  | Const f ->
      if is_float_ty ty then reverse_float (const f) else const f
  | BoolConst b -> bool b
  | Var x ->
      if is_float_ty ty && not (StringSet.mem x env) then
        reverse_float (node (Var x))
      else
        node (Var x)
  | Add (e1, e2) ->
      let yhat1 = value env e1 in
      let yhat2 = value env e2 in
      reverse_float (add (primal yhat1) (primal yhat2))
  | Sub (e1, e2) ->
      let yhat1 = value env e1 in
      let yhat2 = value env e2 in
      reverse_float (sub (primal yhat1) (primal yhat2))
  | Mul (e1, e2) ->
      let yhat1 = value env e1 in
      let yhat2 = value env e2 in
      reverse_float (mul (primal yhat1) (primal yhat2))
  | Div (e1, e2) ->
      let yhat1 = value env e1 in
      let yhat2 = value env e2 in
      reverse_float (div (primal yhat1) (primal yhat2))
  | SpecialFunc (name, args) ->
      let args' = List.map (fun arg -> primal (value env arg)) args in
      reverse_float (special name args')
  | Cmp (op, e1, e2, flipped) ->
      node (Cmp (op, primal (value env e1), primal (value env e2), flipped))
  | FinCmp (op, e1, e2, n, flipped) ->
      node (FinCmp (op, value env e1, value env e2, n, flipped))
  | FinEq (e1, e2, n) ->
      node (FinEq (value env e1, value env e2, n))
  | And (e1, e2) ->
      node (If (value env e1, value env e2, bool false))
  | Or (e1, e2) ->
      node (If (value env e1, bool true, value env e2))
  | Not e1 -> node (Not (value env e1))
  | If (e1, e2, e3) ->
      node (If (value env e1, value env e2, value env e3))
  | Let (x, e1, e2) ->
      node (Let (x, value env e1, value (StringSet.add x env) e2))
  | Pair (e1, e2) -> pair (value env e1) (value env e2)
  | First e1 -> first (value env e1)
  | Second e1 -> second (value env e1)
  | Fun (x, e1) ->
      let k = Util.fresh_var "_rev_k" in
      node
        (Fun
           ( x
           , node
               (Fun
                  ( k
                  , trans (StringSet.add x env) e1
                      (fun v -> node (FuncApp (node (Var k), v))) )) ))
  | FuncApp (e1, e2) ->
      let r = Util.fresh_var "_rev_app" in
      node
        (FuncApp
           ( node (FuncApp (value env e1, value env e2))
           , node (Fun (r, node (Var r))) ))
  | Fix (f, x, e1) ->
      let k = Util.fresh_var "_rev_k" in
      node
        (Fix
           ( f
           , x
           , node
               (Fun
                  ( k
                  , trans (StringSet.add f (StringSet.add x env)) e1
                      (fun v -> node (FuncApp (node (Var k), v))) )) ))
  | FinConst (k, n) -> node (FinConst (k, n))
  | Observe e1 -> node (Observe (value env e1))
  | Nil -> node Nil
  | Cons (e1, e2) -> node (Cons (value env e1, value env e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      node
        (MatchList
           ( value env e1
           , value env e_nil
           , y
           , ys
           , value (StringSet.add y (StringSet.add ys env)) e_cons ))
  | Ref e1 -> ref_ (value env e1)
  | Deref e1 -> deref (value env e1)
  | Assign (e1, e2) -> assign (value env e1) (value env e2)
  | Seq (e1, e2) -> seq (value env e1) (value env e2)
  | Unit -> unit_
  | RuntimeError msg ->
      if is_float_ty ty then reverse_float (node (RuntimeError msg))
      else node (RuntimeError msg)
  | Cdf (dist, point) ->
      reverse_float (node (Cdf (sample_value env dist, primal (value env point))))
  | CdfExpr (kernel, point) ->
      reverse_float (node (CdfExpr (primal (value env kernel), primal (value env point))))
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before reverse AD"
  | DiscreteCase _ ->
      unsupported "discrete reverse AD is not implemented yet"

and trans env ((_, _, TAExprNode ae) as te) k =
  match ae with
  | Add (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              binary_reverse
                add
                (fun yhat _ _ -> adjoint_value yhat)
                (fun yhat _ _ -> adjoint_value yhat)
                yhat1
                yhat2
                k))))
  | Sub (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              binary_reverse
                sub
                (fun yhat _ _ -> adjoint_value yhat)
                (fun yhat _ _ -> sub zero (adjoint_value yhat))
                yhat1
                yhat2
                k))))
  | Mul (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              binary_reverse
                mul
                (fun yhat _ yhat2 -> mul (adjoint_value yhat) (primal yhat2))
                (fun yhat yhat1 _ -> mul (adjoint_value yhat) (primal yhat1))
                yhat1
                yhat2
                k))))
  | Div (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              binary_reverse
                div
                (fun yhat _ yhat2 -> div (adjoint_value yhat) (primal yhat2))
                (fun yhat yhat1 yhat2 ->
                   sub zero
                     (div
                        (mul (adjoint_value yhat) (primal yhat1))
                        (mul (primal yhat2) (primal yhat2))))
                yhat1
                yhat2
                k))))
  | SpecialFunc ("sqrt", [e1]) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          bind_rev "_rev_yhat"
            (reverse_float (special "sqrt" [primal yhat1]))
            (fun yhat ->
               sequence
                 [ k yhat
                 ; add_adjoint yhat1
                     (div (adjoint_value yhat) (mul (const 2.0) (primal yhat)))
                 ])))
  | SpecialFunc (name, _) ->
      unsupported ("reverse differentiation of special function " ^ name ^ " is not implemented")
  | Let (x, e1, e2) ->
      trans env e1 (fun yhat1 ->
        node (Let (x, yhat1, trans (StringSet.add x env) e2 k)))
  | If (e1, e2, e3) ->
      node (If (value env e1, trans env e2 k, trans env e3 k))
  | Pair (e1, e2) ->
      trans env e1 (fun yhat1 ->
        trans env e2 (fun yhat2 -> k (pair yhat1 yhat2)))
  | First e1 ->
      trans env e1 (fun yhat1 -> k (first yhat1))
  | Second e1 ->
      trans env e1 (fun yhat1 -> k (second yhat1))
  | FuncApp (e1, e2) ->
      trans env e1 (fun f ->
        trans env e2 (fun arg ->
          let x = Util.fresh_var "_rev_app" in
          let cont = node (Fun (x, k (node (Var x)))) in
          node (FuncApp (node (FuncApp (f, arg)), cont))))
  | Cons (e1, e2) ->
      trans env e1 (fun yhat1 ->
        trans env e2 (fun yhat2 -> k (node (Cons (yhat1, yhat2)))))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      trans env e1 (fun yhat_match ->
        node
          (MatchList
             ( yhat_match
             , trans env e_nil k
             , y
             , ys
             , trans (StringSet.add y (StringSet.add ys env)) e_cons k )))
  | Ref e1 ->
      trans env e1 (fun yhat1 -> k (ref_ yhat1))
  | Deref e1 ->
      trans env e1 (fun yhat1 -> k (deref yhat1))
  | Assign (e1, e2) ->
      trans env e1 (fun yhat1 ->
        trans env e2 (fun yhat2 -> k (assign yhat1 yhat2)))
  | Seq (e1, e2) ->
      trans env e1 (fun _ -> trans env e2 k)
  | Observe e1 ->
      sequence [node (Observe (value env e1)); k unit_]
  | Cdf _ | CdfExpr _ ->
      unsupported "reverse differentiation of CDF expressions is not implemented yet"
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before reverse AD"
  | DiscreteCase _ ->
      unsupported "discrete reverse AD is not implemented yet"
  | Const _ | BoolConst _ | Var _ | Cmp _ | FinCmp _ | FinEq _
  | And _ | Or _ | Not _ | Fun _ | Fix _ | FinConst _ | Nil | Unit
  | RuntimeError _ ->
      k (value env te)

let diff_var = "theta"

let bind_input name body =
  node (Let (name, reverse_float (node (Var name)), body))

let bind_diff_input body =
  bind_input diff_var body

let diff_gradient () =
  adjoint_value (node (Var diff_var))

let objective result_ref ty zhat =
  match Ast.force ty with
  | TFloat _ ->
      sequence
        [ assign result_ref (primal zhat)
        ; assign (adjoint zhat) one
        ]
  | TBool ->
      assign result_ref (node (If (zhat, one, zero)))
  | _ ->
      unsupported "top-level reverse AD objective must be float- or bool-valued"

let objective_cont result_ref ty zhat =
  if is_float_ty ty then
    bind_rev "_rev_zhat" zhat (objective result_ref ty)
  else
    objective result_ref ty zhat

exception Cannot_interpret_reverse of string

type sym_value =
  | SExpr of expr
  | SPair of sym_value * sym_value
  | SClosure of string * expr * sym_env
  | SRecClosure of string * string * expr * sym_env
  | SRef of sym_value ref
  | SUnit
  | SNil
  | SCons of sym_value * sym_value
and sym_env = (string * sym_value) list

let rec sym_lookup x = function
  | [] -> SExpr (node (Var x))
  | (y, v) :: rest -> if x = y then v else sym_lookup x rest

let rec sym_expr = function
  | SExpr e -> e
  | SPair (v1, v2) -> pair (sym_expr v1) (sym_expr v2)
  | SRef r -> ref_ (sym_expr !r)
  | SUnit -> unit_
  | SNil -> node Nil
  | SCons (v_hd, v_tl) -> node (Cons (sym_expr v_hd, sym_expr v_tl))
  | SClosure (x, body, []) -> node (Fun (x, body))
  | SClosure _ ->
      raise (Cannot_interpret_reverse "cannot reify closure with captured environment")
  | SRecClosure (f, x, body, []) -> node (Fix (f, x, body))
  | SRecClosure _ ->
      raise (Cannot_interpret_reverse "cannot reify recursive closure with captured environment")

let sym_bool = function
  | SExpr (ExprNode (BoolConst b)) -> Some b
  | _ -> None

let sym_arith op v1 v2 =
  SExpr (op (sym_expr v1) (sym_expr v2))

let rec sym_sample env = function
  | Distr1 (kind, e1) -> Distr1 (kind, sym_expr (sym_eval env e1))
  | Distr2 (kind, e1, e2) ->
      Distr2 (kind, sym_expr (sym_eval env e1), sym_expr (sym_eval env e2))

and sym_eval env (ExprNode e) =
  match e with
  | Const f -> SExpr (const f)
  | BoolConst b -> SExpr (bool b)
  | Var x -> sym_lookup x env
  | Let (x, e1, e2) ->
      let v1 = sym_eval env e1 in
      sym_eval ((x, v1) :: env) e2
  | Pair (e1, e2) -> SPair (sym_eval env e1, sym_eval env e2)
  | First e1 ->
      (match sym_eval env e1 with
       | SPair (v1, _) -> v1
       | v -> SExpr (first (sym_expr v)))
  | Second e1 ->
      (match sym_eval env e1 with
       | SPair (_, v2) -> v2
       | v -> SExpr (second (sym_expr v)))
  | Ref e1 -> SRef (ref (sym_eval env e1))
  | Deref e1 ->
      (match sym_eval env e1 with
       | SRef r -> !r
       | v -> SExpr (deref (sym_expr v)))
  | Assign (e1, e2) ->
      (match sym_eval env e1 with
       | SRef r ->
           r := sym_eval env e2;
           SUnit
       | _ ->
           raise (Cannot_interpret_reverse "assignment target is not a ref"))
  | Seq (e1, e2) ->
      let _ = sym_eval env e1 in
      sym_eval env e2
  | Add (e1, e2) -> sym_arith add (sym_eval env e1) (sym_eval env e2)
  | Sub (e1, e2) -> sym_arith sub (sym_eval env e1) (sym_eval env e2)
  | Mul (e1, e2) -> sym_arith mul (sym_eval env e1) (sym_eval env e2)
  | Div (e1, e2) -> sym_arith div (sym_eval env e1) (sym_eval env e2)
  | SpecialFunc (name, args) ->
      SExpr (special name (List.map (fun e -> sym_expr (sym_eval env e)) args))
  | Cmp (op, e1, e2, flipped) ->
      SExpr
        (Simplify.expr
           (node (Cmp (op, sym_expr (sym_eval env e1), sym_expr (sym_eval env e2), flipped))))
  | FinCmp (op, e1, e2, n, flipped) ->
      SExpr
        (Simplify.expr
           (node
              (FinCmp
                 ( op
                 , sym_expr (sym_eval env e1)
                 , sym_expr (sym_eval env e2)
                 , n
                 , flipped ))))
  | FinEq (e1, e2, n) ->
      SExpr
        (Simplify.expr
           (node
              (FinEq
                 ( sym_expr (sym_eval env e1)
                 , sym_expr (sym_eval env e2)
                 , n ))))
  | And (e1, e2) ->
      let v1 = sym_eval env e1 in
      (match sym_bool v1 with
       | Some false -> SExpr (bool false)
       | Some true -> sym_eval env e2
       | None ->
           SExpr
             (node
                (And
                   ( sym_expr v1
                   , sym_expr (sym_eval env e2) ))))
  | Or (e1, e2) ->
      let v1 = sym_eval env e1 in
      (match sym_bool v1 with
       | Some true -> SExpr (bool true)
       | Some false -> sym_eval env e2
       | None ->
           SExpr
             (node
                (Or
                   ( sym_expr v1
                   , sym_expr (sym_eval env e2) ))))
  | Not e1 ->
      let v1 = sym_eval env e1 in
      (match sym_bool v1 with
       | Some b -> SExpr (bool (not b))
       | None -> SExpr (node (Not (sym_expr v1))))
  | If (e1, e2, e3) ->
      (match sym_bool (sym_eval env e1) with
       | Some true -> sym_eval env e2
       | Some false -> sym_eval env e3
       | None ->
           raise
             (Cannot_interpret_reverse
                "cannot choose a branch for a symbolic reverse conditional"))
  | Fun (x, e1) -> SClosure (x, e1, env)
  | FuncApp (e1, e2) ->
      let f = sym_eval env e1 in
      let arg = sym_eval env e2 in
      (match f with
       | SClosure (x, body, captured_env) ->
           sym_eval ((x, arg) :: captured_env) body
       | SRecClosure (f_name, x, body, captured_env) ->
           sym_eval ((x, arg) :: (f_name, f) :: captured_env) body
       | _ -> SExpr (node (FuncApp (sym_expr f, sym_expr arg))))
  | Fix (f, x, e1) -> SRecClosure (f, x, e1, env)
  | FinConst (k, n) -> SExpr (node (FinConst (k, n)))
  | Observe e1 ->
      (match sym_bool (sym_eval env e1) with
       | Some true -> SUnit
       | Some false -> raise (Cannot_interpret_reverse "observe failed")
       | None -> raise (Cannot_interpret_reverse "symbolic observe"))
  | Nil -> SNil
  | Cons (e1, e2) -> SCons (sym_eval env e1, sym_eval env e2)
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      (match sym_eval env e1 with
       | SNil -> sym_eval env e_nil
       | SCons (v_hd, v_tl) -> sym_eval ((y, v_hd) :: (ys, v_tl) :: env) e_cons
       | _ -> raise (Cannot_interpret_reverse "symbolic list match"))
  | Unit -> SUnit
  | RuntimeError msg -> raise (Cannot_interpret_reverse msg)
  | Cdf (dist, point) ->
      SExpr (node (Cdf (sym_sample env dist, sym_expr (sym_eval env point))))
  | CdfExpr (kernel, point) ->
      SExpr
        (node
           (CdfExpr
              ( sym_expr (sym_eval env kernel)
              , sym_expr (sym_eval env point) )))
  | Sample _ ->
      raise (Cannot_interpret_reverse "sample")
  | DiscreteCase _ ->
      raise (Cannot_interpret_reverse "discrete case")

let interpret_effects e =
  try Some (Simplify.algebraic (sym_expr (sym_eval [] e))) with
  | Cannot_interpret_reverse _ -> None

let interpret_effects_or_original e =
  match interpret_effects e with
  | Some e' -> e'
  | None -> e

let dual_expectation_raw ?param ?seeds te =
  let _ = param, seeds in
  if effect_of te = Prob then
    unsupported "probabilistic reverse AD is not implemented yet";
  let result = Util.fresh_var "_rev_result" in
  let result_ref = node (Var result) in
  let ty, _, _ = te in
  let env = StringSet.singleton diff_var in
  bind_diff_input
    (node
       (Let
          ( result
          , ref_ zero
          , sequence
              [ trans env te (objective_cont result_ref ty)
              ; pair (deref result_ref) (diff_gradient ())
              ] )))

let gradient_raw ?param ?seeds te =
  second (dual_expectation_raw ?param ?seeds te)

let dual_expectation ?param ?seeds te =
  interpret_effects_or_original
    (Simplify.algebraic (dual_expectation_raw ?param ?seeds te))

let gradient ?param ?seeds te =
  interpret_effects_or_original
    (Simplify.algebraic (gradient_raw ?param ?seeds te))

let is_closed e =
  Simplify.StringSet.is_empty (Simplify.free_vars e)

let interpret_closed e =
  match interpret_effects e with
  | Some e' -> Some e'
  | None when is_closed e ->
    Some (Simplify.algebraic (Interp.eval_to_expr [] e))
  | None -> None

let interpret_closed_or_original e =
  match interpret_closed e with
  | Some e' -> e'
  | None -> e
