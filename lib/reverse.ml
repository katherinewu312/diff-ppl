(* Reverse-mode AD.

   Float values are represented as [(primal, adjoint_ref)].  The
   The deterministic transformation follows Wang-style direct style:
   it recurses structurally over the source program, and local
   arithmetic nodes use shift/reset to run the rest of the computation
   before performing their local backprop updates.

   Discrete distributions are handled by exact enumeration in CPS.  The
   branch probabilities and branch continuations are combined with the
   same Wang-style reverse primitives used for deterministic arithmetic. *)

open Ast

module StringSet = Util.StringSet
module StringMap = Adev.StringMap

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
let reset e = node (Reset e)
let shift k e = node (Shift (k, e))
let unit_ = node Unit
let zero = const 0.0
let one = const 1.0

let unsupported msg = failwith ("Reverse AD: " ^ msg)

let effect_of (_, eff, _) = Ast.force_effect eff

let is_prob_effect eff =
  match Ast.force_effect eff with
  | Prob -> true
  | Pure | EMeta _ -> false

let function_returns_prob (ty, _, _) =
  match Ast.force ty with
  | TFun (_, eff, _) -> is_prob_effect eff
  | _ -> false

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

let apply_cont k yhat =
  node (FuncApp (node (Var k), yhat))

type binary_rule =
  { primal_op : expr -> expr -> expr
  ; backprop_left : expr -> expr -> expr -> expr
  ; backprop_right : expr -> expr -> expr -> expr
  }

let binary_reverse { primal_op; backprop_left; backprop_right } yhat1 yhat2 =
  let cont = Util.fresh_var "_rev_k" in
  shift cont
    (bind_rev "_rev_yhat"
       (reverse_float (primal_op (primal yhat1) (primal yhat2)))
       (fun yhat ->
          sequence
            [ apply_cont cont yhat
            ; add_adjoint yhat1 (backprop_left yhat yhat1 yhat2)
            ; add_adjoint yhat2 (backprop_right yhat yhat1 yhat2)
            ]))

let addR =
  binary_reverse
    { primal_op = add
    ; backprop_left = (fun yhat _ _ -> adjoint_value yhat)
    ; backprop_right = (fun yhat _ _ -> adjoint_value yhat)
    }

let subR =
  binary_reverse
    { primal_op = sub
    ; backprop_left = (fun yhat _ _ -> adjoint_value yhat)
    ; backprop_right = (fun yhat _ _ -> sub zero (adjoint_value yhat))
    }

let mulR =
  binary_reverse
    { primal_op = mul
    ; backprop_left =
        (fun yhat _ yhat2 -> mul (adjoint_value yhat) (primal yhat2))
    ; backprop_right =
        (fun yhat yhat1 _ -> mul (adjoint_value yhat) (primal yhat1))
    }

let divR =
  binary_reverse
    { primal_op = div
    ; backprop_left =
        (fun yhat _ yhat2 -> div (adjoint_value yhat) (primal yhat2))
    ; backprop_right =
        (fun yhat yhat1 yhat2 ->
           sub zero
             (div
                (mul (adjoint_value yhat) (primal yhat1))
                (mul (primal yhat2) (primal yhat2))))
    }

let rec sumR = function
  | [] -> reverse_float zero
  | [yhat] -> yhat
  | yhat :: rest ->
      bind_rev "_rev_sum" (sumR rest) (fun rest_yhat ->
        addR yhat rest_yhat)

let rec trans_binary env e1 e2 op =
  bind_rev "_rev_yhat" (trans env e1) (fun yhat1 ->
    bind_rev "_rev_yhat" (trans env e2) (fun yhat2 ->
      op yhat1 yhat2))

and trans env (ty, _, TAExprNode ae) =
  match ae with
  | Const f ->
      if Util.is_float_ty ty then reverse_float (const f) else const f
  | BoolConst b ->
      bool b
  | Var x ->
      if Util.is_float_ty ty && not (StringSet.mem x env) then
        reverse_float (node (Var x))
      else
        node (Var x)
  | Add (e1, e2) -> trans_binary env e1 e2 addR
  | Sub (e1, e2) -> trans_binary env e1 e2 subR
  | Mul (e1, e2) -> trans_binary env e1 e2 mulR
  | Div (e1, e2) -> trans_binary env e1 e2 divR
  | SpecialFunc ("sqrt", [e1]) ->
      bind_rev "_rev_yhat" (trans env e1) (fun yhat1 ->
        let cont = Util.fresh_var "_rev_k" in
        shift cont
          (bind_rev "_rev_yhat"
             (reverse_float (special "sqrt" [primal yhat1]))
             (fun yhat ->
                sequence
                  [ apply_cont cont yhat
                  ; add_adjoint yhat1
                      (div
                         (adjoint_value yhat)
                         (mul (const 2.0) (primal yhat)))
                  ])))
  | SpecialFunc (name, _) ->
      unsupported ("reverse differentiation of special function " ^ name ^ " is not implemented")
  | Let (x, e1, e2) ->
      node (Let (x, trans env e1, trans (StringSet.add x env) e2))
  | If (e1, e2, e3) ->
      node (If (trans env e1, trans env e2, trans env e3))
  | Cmp (op, e1, e2, flipped) ->
      bind_rev "_rev_yhat" (trans env e1) (fun yhat1 ->
        bind_rev "_rev_yhat" (trans env e2) (fun yhat2 ->
          node (Cmp (op, primal yhat1, primal yhat2, flipped))))
  | FinCmp (op, e1, e2, n, flipped) ->
      node (FinCmp (op, trans env e1, trans env e2, n, flipped))
  | FinEq (e1, e2, n) ->
      node (FinEq (trans env e1, trans env e2, n))
  | And (e1, e2) ->
      node (If (trans env e1, trans env e2, bool false))
  | Or (e1, e2) ->
      node (If (trans env e1, bool true, trans env e2))
  | Not e1 ->
      node (Not (trans env e1))
  | Pair (e1, e2) ->
      pair (trans env e1) (trans env e2)
  | First e1 ->
      first (trans env e1)
  | Second e1 ->
      second (trans env e1)
  | Fun (x, e1) ->
      if is_prob_effect (effect_of e1) then
        let k = Util.fresh_var "_rev_kappa" in
        node
          (Fun
             ( x
             , node
                 (Fun
                    ( k
                    , prob_trans (StringSet.add x env) e1
                        (fun v -> node (FuncApp (node (Var k), v))) )) ))
      else
        node (Fun (x, trans (StringSet.add x env) e1))
  | FuncApp (e1, e2) ->
      node (FuncApp (trans env e1, trans env e2))
  | Fix (f, x, e1) ->
      node
        (Fix
           ( f
           , x
           , trans (StringSet.add f (StringSet.add x env)) e1 ))
  | FinConst (k, n) ->
      node (FinConst (k, n))
  | Nil ->
      node Nil
  | Cons (e1, e2) ->
      node (Cons (trans env e1, trans env e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      node
        (MatchList
           ( trans env e1
           , trans env e_nil
           , y
           , ys
           , trans (StringSet.add y (StringSet.add ys env)) e_cons ))
  | Ref e1 ->
      ref_ (trans env e1)
  | Deref e1 ->
      deref (trans env e1)
  | Assign (e1, e2) ->
      assign (trans env e1) (trans env e2)
  | Seq (e1, e2) ->
      seq (trans env e1) (trans env e2)
  | Unit ->
      unit_
  | Observe e1 ->
      sequence [node (Observe (trans env e1)); unit_]
  | RuntimeError msg ->
      if Util.is_float_ty ty then reverse_float (node (RuntimeError msg))
      else node (RuntimeError msg)
  | Cdf _ | CdfExpr _ ->
      unsupported "reverse differentiation of CDF expressions is not implemented yet"
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before reverse AD"
  | DiscreteCase _ ->
      unsupported "discrete reverse AD is not implemented yet"
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"

and prob_trans env ((_, _, TAExprNode ae) as te) kappa =
  if not (is_prob_effect (effect_of te)) then
    bind_rev "_rev_yhat" (trans env te) kappa
  else
    match ae with
  | DiscreteCase cases ->
      let rec bind_cases chats = function
        | [] -> sumR (List.rev chats)
        | (branch, prob) :: rest ->
            bind_rev "_rev_phat" (trans env prob) (fun phat ->
              bind_rev "_rev_bhat" (prob_trans env branch kappa) (fun bhat ->
                bind_rev "_rev_chat"
                  (mulR phat bhat)
                  (fun chat -> bind_cases (chat :: chats) rest)))
      in
      bind_cases [] cases

  | Let (x, e1, e2) ->
      if is_prob_effect (effect_of e1) then
        prob_trans env e1 (fun v ->
          node (Let (x, v, prob_trans (StringSet.add x env) e2 kappa)))
      else
        node (Let (x, trans env e1, prob_trans (StringSet.add x env) e2 kappa))

  | If (e1, e2, e3) ->
      if is_prob_effect (effect_of e1) then
        prob_trans env e1 (fun cond ->
          node (If (cond, prob_trans env e2 kappa, prob_trans env e3 kappa)))
      else
        node (If (trans env e1, prob_trans env e2 kappa, prob_trans env e3 kappa))

  | And (e1, e2) ->
      prob_trans env e1 (fun b1 ->
        node (If (b1, prob_trans env e2 kappa, kappa (bool false))))

  | Or (e1, e2) ->
      prob_trans env e1 (fun b1 ->
        node (If (b1, kappa (bool true), prob_trans env e2 kappa)))

  | Not e1 ->
      prob_trans env e1 (fun b1 -> kappa (node (Not b1)))

  | Seq (e1, e2) ->
      if is_prob_effect (effect_of e1) then
        prob_trans env e1 (fun _ -> prob_trans env e2 kappa)
      else
        seq (trans env e1) (prob_trans env e2 kappa)

  | Observe e1 ->
      prob_trans env e1 (fun b ->
        node (Seq (node (Observe b), kappa unit_)))

  | Add (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              bind_rev "_rev_yhat" (addR yhat1 yhat2) kappa))))
  | Sub (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              bind_rev "_rev_yhat" (subR yhat1 yhat2) kappa))))
  | Mul (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              bind_rev "_rev_yhat" (mulR yhat1 yhat2) kappa))))
  | Div (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              bind_rev "_rev_yhat" (divR yhat1 yhat2) kappa))))

  | Cmp (op, e1, e2, flipped) ->
      prob_trans env e1 (fun yhat1 ->
        prob_trans env e2 (fun yhat2 ->
          kappa (node (Cmp (op, primal yhat1, primal yhat2, flipped)))))
  | FinCmp (op, e1, e2, n, flipped) ->
      prob_trans env e1 (fun v1 ->
        prob_trans env e2 (fun v2 ->
          kappa (node (FinCmp (op, v1, v2, n, flipped)))))
  | FinEq (e1, e2, n) ->
      prob_trans env e1 (fun v1 ->
        prob_trans env e2 (fun v2 ->
          kappa (node (FinEq (v1, v2, n)))))

  | Pair (e1, e2) ->
      prob_trans env e1 (fun v1 ->
        prob_trans env e2 (fun v2 -> kappa (pair v1 v2)))
  | First e1 ->
      prob_trans env e1 (fun v -> kappa (first v))
  | Second e1 ->
      prob_trans env e1 (fun v -> kappa (second v))
  | FuncApp (e1, e2) ->
      prob_trans env e1 (fun f ->
        prob_trans env e2 (fun arg ->
          if function_returns_prob e1 then
            let x = Util.fresh_var "_rev_arg" in
            let cont = node (Fun (x, kappa (node (Var x)))) in
            node (FuncApp (node (FuncApp (f, arg)), cont))
          else
            kappa (node (FuncApp (f, arg)))))
  | Cons (e1, e2) ->
      prob_trans env e1 (fun v1 ->
        prob_trans env e2 (fun v2 -> kappa (node (Cons (v1, v2)))))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      prob_trans env e1 (fun v_match ->
        node
          (MatchList
             ( v_match
             , prob_trans env e_nil kappa
             , y
             , ys
             , prob_trans (StringSet.add y (StringSet.add ys env)) e_cons kappa )))

  | Ref e1 ->
      prob_trans env e1 (fun v -> kappa (ref_ v))
  | Deref e1 ->
      prob_trans env e1 (fun v -> kappa (deref v))
  | Assign (e1, e2) ->
      prob_trans env e1 (fun v1 ->
        prob_trans env e2 (fun v2 -> kappa (assign v1 v2)))

  | Cdf _ | CdfExpr _ ->
      unsupported "reverse differentiation of CDF expressions is not implemented yet"
  | Sample _ ->
      unsupported "continuous Sample remained in program; run discretization before reverse AD"
  | Const _ | BoolConst _ | Var _ | Fun _ | Fix _ | FinConst _ | Nil | Unit
  | SpecialFunc _ | RuntimeError _ ->
      kappa (trans env te)
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"

let bind_input name body =
  node (Let (name, reverse_float (node (Var name)), body))

let bind_inputs seeds body =
  StringMap.fold
    (fun name _ acc -> bind_input name acc)
    seeds
    body

let seed_names seeds =
  StringMap.fold (fun name _ acc -> StringSet.add name acc) seeds StringSet.empty

let seed_gradient seeds =
  StringMap.fold
    (fun name seed acc ->
       if seed = 0.0 then acc
       else
         add acc
           (mul
              (const seed)
              (adjoint_value (node (Var name)))))
    seeds
    zero

let seeds_of_params params =
  List.fold_left
    (fun acc param -> add_seed param 1.0 acc)
    no_seeds
    params

let free_float_params te =
  Util.free_float_vars te |> StringSet.elements

let gradient_vector params =
  params
  |> List.map (fun name -> adjoint_value (node (Var name)))
  |> Util.expr_list

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
  if Util.is_float_ty ty then
    bind_rev "_rev_zhat" zhat (objective result_ref ty)
  else
    objective result_ref ty zhat

let expectation_value ty v =
  match Ast.force ty with
  | TFloat _ -> v
  | TBool ->
      reverse_float (node (If (v, one, zero)))
  | _ ->
      unsupported "top-level reverse AD expectation must be float- or bool-valued"

let seed_float_objective result_ref zhat =
  bind_rev "_rev_zhat" zhat (fun zhat ->
    sequence
      [ assign result_ref (primal zhat)
      ; assign (adjoint zhat) one
      ])

exception Cannot_interpret_reverse of string

type sym_value =
  | SExpr of expr
  | SPair of sym_value * sym_value
  | SClosure of string * expr * sym_env
  | SRecClosure of string * string * expr * sym_env
  | SRef of sym_value ref
  | SCont of (sym_value -> sym_value)
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
  | SCont _ ->
      raise (Cannot_interpret_reverse "cannot reify captured continuation")

let sym_bool = function
  | SExpr (ExprNode (BoolConst b)) -> Some b
  | _ -> None

let sym_arith op v1 v2 =
  SExpr (op (sym_expr v1) (sym_expr v2))

let rec sym_sample env = function
  | Distr1 (kind, e1) -> Distr1 (kind, sym_expr (sym_eval env e1))
  | Distr2 (kind, e1, e2) ->
      Distr2 (kind, sym_expr (sym_eval env e1), sym_expr (sym_eval env e2))

and sym_eval env e =
  sym_eval_cps env e (fun v -> v)

and sym_eval_cps env (ExprNode e) k =
  match e with
  | Const f -> k (SExpr (const f))
  | BoolConst b -> k (SExpr (bool b))
  | Var x -> k (sym_lookup x env)
  | Let (x, e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps ((x, v1) :: env) e2 k)
  | Pair (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 -> k (SPair (v1, v2))))
  | First e1 ->
      sym_eval_cps env e1 (function
        | SPair (v1, _) -> k v1
        | v -> k (SExpr (first (sym_expr v))))
  | Second e1 ->
      sym_eval_cps env e1 (function
        | SPair (_, v2) -> k v2
        | v -> k (SExpr (second (sym_expr v))))
  | Ref e1 ->
      sym_eval_cps env e1 (fun v -> k (SRef (ref v)))
  | Deref e1 ->
      sym_eval_cps env e1 (function
        | SRef r -> k !r
        | v -> k (SExpr (deref (sym_expr v))))
  | Assign (e1, e2) ->
      sym_eval_cps env e1 (fun v_ref ->
        sym_eval_cps env e2 (fun v_val ->
          match v_ref with
          | SRef r ->
              r := v_val;
              k SUnit
          | _ ->
              raise (Cannot_interpret_reverse "assignment target is not a ref")))
  | Seq (e1, e2) ->
      sym_eval_cps env e1 (fun _ -> sym_eval_cps env e2 k)
  | Add (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 -> k (sym_arith add v1 v2)))
  | Sub (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 -> k (sym_arith sub v1 v2)))
  | Mul (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 -> k (sym_arith mul v1 v2)))
  | Div (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 -> k (sym_arith div v1 v2)))
  | SpecialFunc (name, args) ->
      let rec eval_args acc = function
        | [] -> k (SExpr (special name (List.rev_map sym_expr acc)))
        | arg :: rest ->
            sym_eval_cps env arg (fun v -> eval_args (v :: acc) rest)
      in
      eval_args [] args
  | Cmp (op, e1, e2, flipped) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 ->
          k
            (SExpr
               (Simplify.expr
                  (node (Cmp (op, sym_expr v1, sym_expr v2, flipped)))))))
  | FinCmp (op, e1, e2, n, flipped) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 ->
          k
            (SExpr
               (Simplify.expr
                  (node (FinCmp (op, sym_expr v1, sym_expr v2, n, flipped)))))))
  | FinEq (e1, e2, n) ->
      sym_eval_cps env e1 (fun v1 ->
        sym_eval_cps env e2 (fun v2 ->
          k
            (SExpr
               (Simplify.expr
                  (node (FinEq (sym_expr v1, sym_expr v2, n)))))))
  | And (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        match sym_bool v1 with
        | Some false -> k (SExpr (bool false))
        | Some true -> sym_eval_cps env e2 k
        | None ->
            sym_eval_cps env e2 (fun v2 ->
              k (SExpr (node (And (sym_expr v1, sym_expr v2))))))
  | Or (e1, e2) ->
      sym_eval_cps env e1 (fun v1 ->
        match sym_bool v1 with
        | Some true -> k (SExpr (bool true))
        | Some false -> sym_eval_cps env e2 k
        | None ->
            sym_eval_cps env e2 (fun v2 ->
              k (SExpr (node (Or (sym_expr v1, sym_expr v2))))))
  | Not e1 ->
      sym_eval_cps env e1 (fun v1 ->
        match sym_bool v1 with
        | Some b -> k (SExpr (bool (not b)))
        | None -> k (SExpr (node (Not (sym_expr v1)))))
  | If (e1, e2, e3) ->
      sym_eval_cps env e1 (fun v_cond ->
        match sym_bool v_cond with
        | Some true -> sym_eval_cps env e2 k
        | Some false -> sym_eval_cps env e3 k
        | None ->
            raise
              (Cannot_interpret_reverse
                 "cannot choose a branch for a symbolic reverse conditional"))
  | Fun (x, e1) -> k (SClosure (x, e1, env))
  | FuncApp (e1, e2) ->
      sym_eval_cps env e1 (fun f ->
        sym_eval_cps env e2 (fun arg ->
          match f with
          | SClosure (x, body, captured_env) ->
              sym_eval_cps ((x, arg) :: captured_env) body k
          | SRecClosure (f_name, x, body, captured_env) ->
              sym_eval_cps ((x, arg) :: (f_name, f) :: captured_env) body k
          | SCont captured ->
              k (captured arg)
          | _ -> k (SExpr (node (FuncApp (sym_expr f, sym_expr arg))))))
  | Fix (f, x, e1) -> k (SRecClosure (f, x, e1, env))
  | FinConst (i, n) -> k (SExpr (node (FinConst (i, n))))
  | Observe e1 ->
      sym_eval_cps env e1 (fun v1 ->
        match sym_bool v1 with
        | Some true -> k SUnit
        | Some false -> raise (Cannot_interpret_reverse "observe failed")
        | None -> raise (Cannot_interpret_reverse "symbolic observe"))
  | Nil -> k SNil
  | Cons (e1, e2) ->
      sym_eval_cps env e1 (fun v_hd ->
        sym_eval_cps env e2 (fun v_tl -> k (SCons (v_hd, v_tl))))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      sym_eval_cps env e1 (function
        | SNil -> sym_eval_cps env e_nil k
        | SCons (v_hd, v_tl) ->
            sym_eval_cps ((y, v_hd) :: (ys, v_tl) :: env) e_cons k
        | _ -> raise (Cannot_interpret_reverse "symbolic list match"))
  | Unit -> k SUnit
  | RuntimeError msg -> raise (Cannot_interpret_reverse msg)
  | Reset e1 ->
      let v = sym_eval_cps env e1 (fun v -> v) in
      k v
  | Shift (cont_name, body) ->
      sym_eval_cps ((cont_name, SCont k) :: env) body (fun v -> v)
  | Cdf (dist, point) ->
      sym_eval_cps env point (fun v_point ->
        k (SExpr (node (Cdf (sym_sample env dist, sym_expr v_point)))))
  | CdfExpr (kernel, point) ->
      sym_eval_cps env kernel (fun v_kernel ->
        sym_eval_cps env point (fun v_point ->
          let e = node (CdfExpr (sym_expr v_kernel, sym_expr v_point)) in
          k (SExpr e)))
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

let dual_expectation_with_gradient seeds gradient te =
  let result = Util.fresh_var "_rev_result" in
  let result_ref = node (Var result) in
  let ty, _, _ = te in
  let env = seed_names seeds in
  let transformed =
    match effect_of te with
    | Prob ->
        prob_trans env te (expectation_value ty)
        |> seed_float_objective result_ref
    | Pure | EMeta _ ->
        objective_cont result_ref ty (trans env te)
  in
  bind_inputs seeds
    (node
       (Let
          ( result
          , ref_ zero
          , sequence
              [ reset transformed
              ; pair (deref result_ref) gradient
              ] )))

let dual_expectation_with_seeds seeds te =
  dual_expectation_with_gradient seeds (seed_gradient seeds) te

let dual_expectation_vector_raw te =
  let params = free_float_params te in
  dual_expectation_with_gradient
    (seeds_of_params params)
    (gradient_vector params)
    te

let dual_expectation_raw ?param ?seeds te =
  match seeds, param with
  | Some seeds, _ -> dual_expectation_with_seeds seeds te
  | None, Some param -> dual_expectation_with_seeds (seeds_of_param param) te
  | None, None -> dual_expectation_vector_raw te

let gradient_raw ?param ?seeds te =
  match seeds, param with
  | Some seeds, _ -> second (dual_expectation_with_seeds seeds te)
  | None, Some param -> second (dual_expectation_with_seeds (seeds_of_param param) te)
  | None, None -> second (dual_expectation_vector_raw te)

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

(* Concrete reverse-mode evaluator.

   This path intentionally reuses the source-to-source reverse AD program
   above.  It substitutes concrete input values into [gradient_raw], then
   evaluates that generated program with concrete values and real support for
   the generated [shift]/[reset] nodes. *)

type runtime_value =
  | RBool of bool
  | RFloat of float
  | RPair of runtime_value * runtime_value
  | RFin of int * int
  | RClosure of string * expr * runtime_env
  | RRecClosure of string * string * expr * runtime_env
  | RCont of (runtime_value -> runtime_value)
  | RUnit
  | RNil
  | RCons of runtime_value * runtime_value
  | RRef of runtime_value ref
and runtime_env = (string * runtime_value) list

let runtime_error msg = failwith ("Reverse runtime AD: " ^ msg)

let runtime_lookup x env =
  match List.assoc_opt x env with
  | Some v -> v
  | None -> runtime_error ("unbound variable " ^ x)

let runtime_as_float = function
  | RFloat f -> f
  | _ -> runtime_error "expected float"

let runtime_as_bool = function
  | RBool b -> b
  | _ -> runtime_error "expected bool"

let runtime_as_fin = function
  | RFin (k, n) -> (k, n)
  | _ -> runtime_error "expected finite value"

let runtime_as_ref = function
  | RRef r -> r
  | _ -> runtime_error "expected ref"

let runtime_arith op v1 v2 =
  RFloat (op (runtime_as_float v1) (runtime_as_float v2))

let rec runtime_eval_dist env dist =
  match dist with
  | Distr1 (kind, e1) ->
      let f1 = runtime_as_float (runtime_eval env e1) in
      (match Distributions.get_cdistr_from_single_arg_kind kind f1 with
       | Ok dist -> dist
       | Error msg -> runtime_error msg)
  | Distr2 (kind, e1, e2) ->
      let f1 = runtime_as_float (runtime_eval env e1) in
      let f2 = runtime_as_float (runtime_eval env e2) in
      (match Distributions.get_cdistr_from_two_arg_kind kind f1 f2 with
       | Ok dist -> dist
       | Error msg -> runtime_error msg)

and runtime_eval env e =
  runtime_eval_cps env e (fun v -> v)

and runtime_eval_cps env (ExprNode e) k =
  match e with
  | Const f -> k (RFloat f)
  | BoolConst b -> k (RBool b)
  | Var x -> k (runtime_lookup x env)
  | Let (x, e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps ((x, v1) :: env) e2 k)
  | Pair (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 -> k (RPair (v1, v2))))
  | First e1 ->
      runtime_eval_cps env e1 (function
        | RPair (v1, _) -> k v1
        | _ -> runtime_error "fst expected a pair")
  | Second e1 ->
      runtime_eval_cps env e1 (function
        | RPair (_, v2) -> k v2
        | _ -> runtime_error "snd expected a pair")
  | Ref e1 ->
      runtime_eval_cps env e1 (fun v -> k (RRef (ref v)))
  | Deref e1 ->
      runtime_eval_cps env e1 (fun v -> k !(runtime_as_ref v))
  | Assign (e1, e2) ->
      runtime_eval_cps env e1 (fun v_ref ->
        runtime_eval_cps env e2 (fun v_val ->
          runtime_as_ref v_ref := v_val;
          k RUnit))
  | Seq (e1, e2) ->
      runtime_eval_cps env e1 (fun _ -> runtime_eval_cps env e2 k)
  | Add (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 -> k (runtime_arith (+.) v1 v2)))
  | Sub (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 -> k (runtime_arith (-.) v1 v2)))
  | Mul (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 -> k (runtime_arith ( *. ) v1 v2)))
  | Div (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 -> k (runtime_arith (/.) v1 v2)))
  | SpecialFunc (name, args) ->
      runtime_eval_args env args (fun values ->
        let floats = List.map runtime_as_float values in
        match Simplify.special_value name floats with
        | Some f -> k (RFloat f)
        | None -> runtime_error ("unknown special function " ^ name))
  | Cmp (op, e1, e2, _) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 ->
          let f1 = runtime_as_float v1 in
          let f2 = runtime_as_float v2 in
          k (RBool (match op with Lt -> f1 < f2 | Le -> f1 <= f2))))
  | FinCmp (op, e1, e2, n, _) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 ->
          let k1, n1 = runtime_as_fin v1 in
          let k2, n2 = runtime_as_fin v2 in
          if n1 <> n || n2 <> n then runtime_error "finite comparison modulus mismatch";
          k (RBool (match op with Lt -> k1 < k2 | Le -> k1 <= k2))))
  | FinEq (e1, e2, n) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 ->
          let k1, n1 = runtime_as_fin v1 in
          let k2, n2 = runtime_as_fin v2 in
          if n1 <> n || n2 <> n then runtime_error "finite equality modulus mismatch";
          k (RBool (k1 = k2))))
  | And (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        if runtime_as_bool v1 then runtime_eval_cps env e2 k else k (RBool false))
  | Or (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        if runtime_as_bool v1 then k (RBool true) else runtime_eval_cps env e2 k)
  | Not e1 ->
      runtime_eval_cps env e1 (fun v1 -> k (RBool (not (runtime_as_bool v1))))
  | If (e1, e2, e3) ->
      runtime_eval_cps env e1 (fun v1 ->
        if runtime_as_bool v1 then runtime_eval_cps env e2 k
        else runtime_eval_cps env e3 k)
  | Fun (x, body) -> k (RClosure (x, body, env))
  | FuncApp (e1, e2) ->
      runtime_eval_cps env e1 (fun f ->
        runtime_eval_cps env e2 (fun arg ->
          match f with
          | RClosure (x, body, captured_env) ->
              runtime_eval_cps ((x, arg) :: captured_env) body k
          | RRecClosure (f_name, x, body, captured_env) ->
              runtime_eval_cps ((x, arg) :: (f_name, f) :: captured_env) body k
          | RCont captured -> k (captured arg)
          | _ -> runtime_error "function application expected a closure"))
  | Fix (f, x, body) -> k (RRecClosure (f, x, body, env))
  | FinConst (i, n) -> k (RFin (i, n))
  | Nil -> k RNil
  | Cons (e1, e2) ->
      runtime_eval_cps env e1 (fun v1 ->
        runtime_eval_cps env e2 (fun v2 -> k (RCons (v1, v2))))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      runtime_eval_cps env e1 (function
        | RNil -> runtime_eval_cps env e_nil k
        | RCons (hd, tl) ->
            runtime_eval_cps ((y, hd) :: (ys, tl) :: env) e_cons k
        | _ -> runtime_error "list match expected a list")
  | Unit -> k RUnit
  | Observe e1 ->
      runtime_eval_cps env e1 (fun v1 ->
        if runtime_as_bool v1 then k RUnit else runtime_error "observe failed")
  | RuntimeError msg -> runtime_error msg
  | Reset e1 ->
      let v = runtime_eval_cps env e1 (fun v -> v) in
      k v
  | Shift (cont_name, body) ->
      runtime_eval_cps ((cont_name, RCont k) :: env) body (fun v -> v)
  | Sample _ ->
      runtime_error "continuous sampling is not supported by the concrete reverse evaluator"
  | DiscreteCase _ ->
      runtime_error "discrete case reached concrete reverse program evaluator"
  | Cdf (dist, point) ->
      let dist = runtime_eval_dist env dist in
      runtime_eval_cps env point (fun v_point ->
        k (RFloat (Distributions.cdistr_cdf dist (runtime_as_float v_point))))
  | CdfExpr _ ->
      runtime_error "CdfExpr is not supported by the concrete reverse evaluator"

and runtime_eval_args env args k =
  match args with
  | [] -> k []
  | arg :: rest ->
      runtime_eval_cps env arg (fun value ->
        runtime_eval_args env rest (fun values -> k (value :: values)))

let runtime_value_lookup name values =
  match List.assoc_opt name values with
  | Some v -> v
  | None ->
      runtime_error
        ("missing concrete value for free float variable " ^ name)

let rec runtime_float_list = function
  | RNil -> []
  | RCons (RFloat f, rest) -> f :: runtime_float_list rest
  | _ -> runtime_error "gradient result should be a float list"

let subst_runtime_values values e =
  List.fold_left
    (fun acc (name, value) -> Simplify.subst_float name value acc)
    e
    values

let runtime_gradient_raw values te =
  gradient_raw te |> subst_runtime_values values

let runtime_gradient_values values te =
  let params = free_float_params te in
  List.iter (fun name -> ignore (runtime_value_lookup name values)) params;
  runtime_gradient_raw values te
  |> runtime_eval []
  |> runtime_float_list

let runtime_gradient values te =
  runtime_gradient_values values te
  |> List.map const
  |> Util.expr_list
