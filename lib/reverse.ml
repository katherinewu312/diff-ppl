(* Reverse-mode AD.

   Float values are represented as [(primal, adjoint_ref)].  The
   transformation is continuation-based: local arithmetic nodes call
   the continuation first, which seeds/propagates adjoints through the
   rest of the program, then perform their local backprop updates.

   Discrete distributions are handled by exact enumeration in CPS.  The
   branch probabilities and branch continuations are combined with the
   same Wang-style reverse primitives used for deterministic arithmetic. *)

open Ast

module StringSet = Adev.StringSet
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

let is_float_ty ty =
  match Ast.force ty with
  | TFloat _ -> true
  | _ -> false

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

let binary_reverse primal_op back1 back2 yhat1 yhat2 k =
  let cont = Util.fresh_var "_rev_k" in
  k
    (shift cont
       (bind_rev "_rev_yhat"
          (reverse_float (primal_op (primal yhat1) (primal yhat2)))
          (fun yhat ->
             sequence
               [ apply_cont cont yhat
               ; add_adjoint yhat1 (back1 yhat yhat1 yhat2)
               ; add_adjoint yhat2 (back2 yhat yhat1 yhat2)
               ])))

let addR yhat1 yhat2 k =
  binary_reverse
    add
    (fun yhat _ _ -> adjoint_value yhat)
    (fun yhat _ _ -> adjoint_value yhat)
    yhat1
    yhat2
    k

let subR yhat1 yhat2 k =
  binary_reverse
    sub
    (fun yhat _ _ -> adjoint_value yhat)
    (fun yhat _ _ -> sub zero (adjoint_value yhat))
    yhat1
    yhat2
    k

let mulR yhat1 yhat2 k =
  binary_reverse
    mul
    (fun yhat _ yhat2 -> mul (adjoint_value yhat) (primal yhat2))
    (fun yhat yhat1 _ -> mul (adjoint_value yhat) (primal yhat1))
    yhat1
    yhat2
    k

let divR yhat1 yhat2 k =
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
    k

let rec sumR = function
  | [] -> reverse_float zero
  | [yhat] -> yhat
  | yhat :: rest ->
      bind_rev "_rev_sum" (sumR rest) (fun rest_yhat ->
        addR yhat rest_yhat (fun sum_yhat -> sum_yhat))

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
        node (Fun (x, trans (StringSet.add x env) e1 (fun v -> v)))
  | FuncApp (e1, e2) ->
      node (FuncApp (value env e1, value env e2))
  | Fix (f, x, e1) ->
      node
        (Fix
           ( f
           , x
           , trans (StringSet.add f (StringSet.add x env)) e1 (fun v -> v) ))
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
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"

and trans env ((_, _, TAExprNode ae) as te) k =
  match ae with
  | Add (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              addR yhat1 yhat2 k))))
  | Sub (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              subR yhat1 yhat2 k))))
  | Mul (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              mulR yhat1 yhat2 k))))
  | Div (e1, e2) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              divR yhat1 yhat2 k))))
  | SpecialFunc ("sqrt", [e1]) ->
      trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          let cont = Util.fresh_var "_rev_k" in
          k
            (shift cont
               (bind_rev "_rev_yhat"
                  (reverse_float (special "sqrt" [primal yhat1]))
                  (fun yhat ->
                     sequence
                       [ apply_cont cont yhat
                       ; add_adjoint yhat1
                           (div
                              (adjoint_value yhat)
                              (mul (const 2.0) (primal yhat)))
                       ])))))
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
          k (node (FuncApp (f, arg)))))
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
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"

and prob_trans env ((_, _, TAExprNode ae) as te) kappa =
  match ae with
  | DiscreteCase cases ->
      let rec bind_cases chats = function
        | [] -> sumR (List.rev chats)
        | (branch, prob) :: rest ->
            trans env prob (fun phat_raw ->
              bind_rev "_rev_phat" phat_raw (fun phat ->
                bind_rev "_rev_bhat" (prob_trans env branch kappa) (fun bhat ->
                  bind_rev "_rev_chat"
                    (mulR phat bhat (fun chat -> chat))
                    (fun chat -> bind_cases (chat :: chats) rest))))
      in
      bind_cases [] cases

  | Let (x, e1, e2) ->
      prob_trans env e1 (fun v ->
        node (Let (x, v, prob_trans (StringSet.add x env) e2 kappa)))

  | If (e1, e2, e3) ->
      prob_trans env e1 (fun cond ->
        node (If (cond, prob_trans env e2 kappa, prob_trans env e3 kappa)))

  | And (e1, e2) ->
      prob_trans env e1 (fun b1 ->
        node (If (b1, prob_trans env e2 kappa, kappa (bool false))))

  | Or (e1, e2) ->
      prob_trans env e1 (fun b1 ->
        node (If (b1, kappa (bool true), prob_trans env e2 kappa)))

  | Not e1 ->
      prob_trans env e1 (fun b1 -> kappa (node (Not b1)))

  | Seq (e1, e2) ->
      prob_trans env e1 (fun _ -> prob_trans env e2 kappa)

  | Observe e1 ->
      prob_trans env e1 (fun b ->
        node (Seq (node (Observe b), kappa unit_)))

  | Add (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              addR yhat1 yhat2 kappa))))
  | Sub (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              subR yhat1 yhat2 kappa))))
  | Mul (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              mulR yhat1 yhat2 kappa))))
  | Div (e1, e2) ->
      prob_trans env e1 (fun yhat1_raw ->
        bind_rev "_rev_yhat" yhat1_raw (fun yhat1 ->
          prob_trans env e2 (fun yhat2_raw ->
            bind_rev "_rev_yhat" yhat2_raw (fun yhat2 ->
              divR yhat1 yhat2 kappa))))

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
      kappa (value env te)
  | Reset _ | Shift _ ->
      unsupported "shift/reset are internal reverse-AD constructs"

let diff_var = "theta"

let bind_input name body =
  node (Let (name, reverse_float (node (Var name)), body))

let bind_inputs seeds body =
  StringMap.fold
    (fun name _ acc -> bind_input name acc)
    seeds
    body

let default_seeds =
  seeds_of_param diff_var

let resolve_seeds ?param ?seeds () =
  match seeds, param with
  | Some seeds, _ -> seeds
  | None, Some param -> seeds_of_param param
  | None, None -> default_seeds

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

let dual_expectation_raw ?param ?seeds te =
  let seeds = resolve_seeds ?param ?seeds () in
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
        trans env te (objective_cont result_ref ty)
  in
  bind_inputs seeds
    (node
       (Let
          ( result
          , ref_ zero
          , sequence
              [ reset transformed
              ; pair (deref result_ref) (seed_gradient seeds)
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
