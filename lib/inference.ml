(* General type/effect elaboration for Slice programs.

   Float types still use [Ast.TFloat] so the existing typed AST remains the
   interchange format between passes, but this module does not populate or
   propagate discretization cuts, concrete values, or symbolic values.  That
   work belongs to [Cut_inference]. *)

open Ast

module StringMap = Map.Make(String)

type typed_expr = texpr

let fresh_float_ty () =
  TFloat
    ( Ast.fresh_cut_bag ()
    , Lats.fresh_float_bag ()
    , Ast.fresh_sym_bag () )

(* Enforce [t_sub <: t_super] using only type shape and effects. *)
let rec sub_type (t_sub : ty) (t_super : ty) : unit =
  match Ast.force t_sub, Ast.force t_super with
  | TBool, TBool
  | TUnit, TUnit
  | TFloat _, TFloat _ -> ()
  | TFin n1, TFin n2 when n1 = n2 -> ()
  | TPair (a1, b1), TPair (a2, b2) ->
      sub_type a1 a2;
      sub_type b1 b2
  | TFun (a1, eff1, b1), TFun (a2, eff2, b2) ->
      sub_type a2 a1;
      Ast.effect_leq eff1 eff2;
      sub_type b1 b2
  | TList t1, TList t2 -> sub_type t1 t2
  | TRef t1, TRef t2 -> unify t1 t2
  | TMeta r, _ ->
      (match Ast.force t_super with
       | TMeta r' ->
           Ast.listen r (fun t -> sub_type t t_super);
           Ast.listen r' (fun t' -> sub_type t_sub t')
       | TBool -> Ast.assign r TBool
       | TFin n -> Ast.assign r (TFin n)
       | TPair _ ->
           let a = Ast.fresh_meta () in
           let b = Ast.fresh_meta () in
           Ast.assign r (TPair (a, b));
           sub_type t_sub t_super
       | TFun _ ->
           let a = Ast.fresh_meta () in
           let b = Ast.fresh_meta () in
           Ast.assign r (TFun (a, Ast.fresh_effect (), b));
           sub_type t_sub t_super
       | TFloat _ ->
           Ast.assign r (fresh_float_ty ());
           sub_type t_sub t_super
       | TUnit -> Ast.assign r TUnit
       | TList _ ->
           let elem = Ast.fresh_meta () in
           Ast.assign r (TList elem);
           sub_type t_sub t_super
       | TRef _ ->
           let elem = Ast.fresh_meta () in
           Ast.assign r (TRef elem);
           sub_type t_sub t_super)
  | _, TMeta r ->
      (match Ast.force t_sub with
       | TMeta r' ->
           Ast.listen r (fun t -> sub_type t_sub t);
           Ast.listen r' (fun t' -> sub_type t' t_super)
       | TBool -> Ast.assign r TBool
       | TFin n -> Ast.assign r (TFin n)
       | TPair _ ->
           let a = Ast.fresh_meta () in
           let b = Ast.fresh_meta () in
           Ast.assign r (TPair (a, b));
           sub_type t_sub t_super
       | TFun _ ->
           let a = Ast.fresh_meta () in
           let b = Ast.fresh_meta () in
           Ast.assign r (TFun (a, Ast.fresh_effect (), b));
           sub_type t_sub t_super
       | TFloat _ ->
           Ast.assign r (fresh_float_ty ());
           sub_type t_sub t_super
       | TUnit -> Ast.assign r TUnit
       | TList _ ->
           let elem = Ast.fresh_meta () in
           Ast.assign r (TList elem);
           sub_type t_sub t_super
       | TRef _ ->
           let elem = Ast.fresh_meta () in
           Ast.assign r (TRef elem);
           sub_type t_sub t_super)
  | _, _ ->
      failwith
        (Printf.sprintf
           "Type mismatch: cannot subtype %s <: %s"
           (Pretty.string_of_ty t_sub)
           (Pretty.string_of_ty t_super))

and unify (t1 : ty) (t2 : ty) : unit =
  try
    sub_type t1 t2;
    sub_type t2 t1
  with Failure msg ->
    failwith
      (Printf.sprintf
         "Type mismatch: cannot unify %s and %s\n(Subtyping error: %s)"
         (Pretty.string_of_ty t1)
         (Pretty.string_of_ty t2)
         msg)

let expect_float ty error =
  try sub_type ty (fresh_float_ty ()) with
  | Failure msg -> failwith (error msg)

let infer (e : expr) : typed_expr =
  let mk ty eff ae = (ty, eff, TAExprNode ae) in
  let pure ty ae = mk ty Pure ae in
  let prob ty ae = mk ty Prob ae in
  let eff_of (_, eff, _) = eff in
  let join = Ast.join_effects in
  let rec aux (env : ty StringMap.t) (orig_expr : expr) : texpr =
    let ExprNode node = orig_expr in
    match node with
    | Const f -> pure (fresh_float_ty ()) (Const f)
    | BoolConst b -> pure TBool (BoolConst b)
    | Var x ->
        let ty =
          match StringMap.find_opt x env with
          | Some ty -> ty
          | None -> fresh_float_ty ()
        in
        pure ty (Var x)
    | Let (x, e1, e2) ->
        let ((t1, eff1, a1) as te1) = aux env e1 in
        let ((t2, eff2, a2) as te2) = aux (StringMap.add x t1 env) e2 in
        ignore te1;
        ignore te2;
        mk t2 (join [eff1; eff2])
          (Let (x, (t1, eff1, a1), (t2, eff2, a2)))
    | Add (e1, e2) -> arith_aux env e1 e2 (fun a b -> Add (a, b))
    | Sub (e1, e2) -> arith_aux env e1 e2 (fun a b -> Sub (a, b))
    | Mul (e1, e2) -> arith_aux env e1 e2 (fun a b -> Mul (a, b))
    | Div (e1, e2) -> arith_aux env e1 e2 (fun a b -> Div (a, b))
    | SpecialFunc (name, args) ->
        let typed_args =
          List.map
            (fun arg ->
               let ((ty, _, _) as typed) = aux env arg in
               expect_float ty
                 (fun msg ->
                    "Type error in special function " ^ name ^ ": " ^ msg);
               typed)
            args
        in
        mk (fresh_float_ty ())
          (join (List.map eff_of typed_args))
          (SpecialFunc (name, typed_args))
    | Cdf (dist, point) ->
        let infer_arg arg name =
          let ((ty, _, _) as typed) = aux env arg in
          expect_float ty
            (fun msg -> "Type error in CDF " ^ name ^ ": " ^ msg);
          typed
        in
        let typed_dist =
          match dist with
          | Distr1 (kind, e1) ->
              Distr1 (kind, infer_arg e1 "distribution argument")
          | Distr2 (kind, e1, e2) ->
              Distr2
                ( kind
                , infer_arg e1 "first distribution argument"
                , infer_arg e2 "second distribution argument" )
        in
        let typed_point = infer_arg point "point argument" in
        let dist_eff =
          match typed_dist with
          | Distr1 (_, te1) -> eff_of te1
          | Distr2 (_, te1, te2) -> join [eff_of te1; eff_of te2]
        in
        mk (fresh_float_ty ())
          (join [dist_eff; eff_of typed_point])
          (Cdf (typed_dist, typed_point))
    | CdfExpr (kernel, point) ->
        let infer_arg arg name =
          let ((ty, _, _) as typed) = aux env arg in
          expect_float ty
            (fun msg ->
               "Type error in CDF expression " ^ name ^ ": " ^ msg);
          typed
        in
        let typed_kernel = infer_arg kernel "kernel argument" in
        let typed_point = infer_arg point "point argument" in
        mk (fresh_float_ty ())
          (join [eff_of typed_kernel; eff_of typed_point])
          (CdfExpr (typed_kernel, typed_point))
    | Sample dist ->
        let typed_dist =
          match dist with
          | Distr1 (kind, arg) ->
              let ((ty, _, _) as typed_arg) = aux env arg in
              expect_float ty
                (fun msg ->
                   let sample = ExprNode (Sample (Distr1 (kind, arg))) in
                   Printf.sprintf
                     "Type error in Sample (%s) argument: %s"
                     (Pretty.string_of_expr_indented sample)
                     msg);
              Distr1 (kind, typed_arg)
          | Distr2 (kind, arg1, arg2) ->
              let ((ty1, _, _) as typed_arg1) = aux env arg1 in
              let ((ty2, _, _) as typed_arg2) = aux env arg2 in
              let sample = ExprNode (Sample (Distr2 (kind, arg1, arg2))) in
              expect_float ty1
                (fun msg ->
                   Printf.sprintf
                     "Type error in Sample (%s) first argument: %s"
                     (Pretty.string_of_expr_indented sample)
                     msg);
              expect_float ty2
                (fun msg ->
                   Printf.sprintf
                     "Type error in Sample (%s) second argument: %s"
                     (Pretty.string_of_expr_indented sample)
                     msg);
              Distr2 (kind, typed_arg1, typed_arg2)
        in
        prob (fresh_float_ty ()) (Sample typed_dist)
    | DiscreteCase cases ->
        if cases = [] then failwith "DiscreteCase cannot be empty";
        let result_ty = Ast.fresh_meta () in
        let typed_cases =
          List.map
            (fun (branch, probability) ->
               let ((branch_ty, _, _) as typed_branch) = aux env branch in
               (try sub_type branch_ty result_ty with
                | Failure msg ->
                    failwith ("Type error in DiscreteCase branches: " ^ msg));
               let ((prob_ty, _, _) as typed_probability) =
                 aux env probability
               in
               expect_float prob_ty
                 (fun msg ->
                    "Type error in DiscreteCase probability: " ^ msg);
               (typed_branch, typed_probability))
            cases
        in
        prob result_ty (DiscreteCase typed_cases)
    | Cmp (op, e1, e2, flipped) ->
        let ((t1, eff1, a1) as te1) = aux env e1 in
        let ((t2, eff2, a2) as te2) = aux env e2 in
        ignore te1;
        ignore te2;
        expect_float t1
          (fun msg -> "Type error in comparison left operand: " ^ msg);
        expect_float t2
          (fun msg -> "Type error in comparison right operand: " ^ msg);
        mk TBool (join [eff1; eff2])
          (Cmp (op, (t1, eff1, a1), (t2, eff2, a2), flipped))
    | FinCmp (op, e1, e2, n, flipped) ->
        if n <= 0 then
          failwith
            (Printf.sprintf "Invalid FinCmp modulus: ==#%d. n must be > 0." n);
        let ((t1, eff1, a1) as te1) = aux env e1 in
        let ((t2, eff2, a2) as te2) = aux env e2 in
        ignore te1;
        ignore te2;
        (try sub_type t1 (TFin n) with
         | Failure msg ->
             failwith
               (Printf.sprintf
                  "Type error in FinCmp (==#%d) left operand: %s" n msg));
        (try sub_type t2 (TFin n) with
         | Failure msg ->
             failwith
               (Printf.sprintf
                  "Type error in FinCmp (==#%d) right operand: %s" n msg));
        mk TBool (join [eff1; eff2])
          (FinCmp (op, (t1, eff1, a1), (t2, eff2, a2), n, flipped))
    | If (condition, then_, else_) ->
        let ((tc, effc, ac) as typed_condition) = aux env condition in
        ignore typed_condition;
        (try sub_type tc TBool with
         | Failure msg -> failwith ("Type error in If condition: " ^ msg));
        let ((tt, efft, at) as typed_then) = aux env then_ in
        let ((te, effe, ae) as typed_else) = aux env else_ in
        ignore typed_then;
        ignore typed_else;
        let result_ty = Ast.fresh_meta () in
        (try
           sub_type tt result_ty;
           sub_type te result_ty
         with Failure msg -> failwith ("Type error in If branches: " ^ msg));
        mk result_ty (join [effc; efft; effe])
          (If ((tc, effc, ac), (tt, efft, at), (te, effe, ae)))
    | Pair (e1, e2) ->
        let ((t1, eff1, a1) as te1) = aux env e1 in
        let ((t2, eff2, a2) as te2) = aux env e2 in
        ignore te1;
        ignore te2;
        mk (TPair (t1, t2)) (join [eff1; eff2])
          (Pair ((t1, eff1, a1), (t2, eff2, a2)))
    | First e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        let left = Ast.fresh_meta () in
        let right = Ast.fresh_meta () in
        (try sub_type ty (TPair (left, right)) with
         | Failure msg -> failwith ("Type error in First (fst): " ^ msg));
        mk (Ast.force left) eff (First (ty, eff, a))
    | Second e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        let left = Ast.fresh_meta () in
        let right = Ast.fresh_meta () in
        (try sub_type ty (TPair (left, right)) with
         | Failure msg -> failwith ("Type error in Second (snd): " ^ msg));
        mk (Ast.force right) eff (Second (ty, eff, a))
    | Fun (x, body) ->
        let param_ty = Ast.fresh_meta () in
        let ((body_ty, body_eff, body_a) as typed_body) =
          aux (StringMap.add x param_ty env) body
        in
        ignore typed_body;
        pure (TFun (param_ty, body_eff, body_ty))
          (Fun (x, (body_ty, body_eff, body_a)))
    | FuncApp (fn, arg) ->
        let ((fn_ty, fn_eff, fn_a) as typed_fn) = aux env fn in
        let ((arg_ty, arg_eff, arg_a) as typed_arg) = aux env arg in
        ignore typed_fn;
        ignore typed_arg;
        let param_ty = Ast.fresh_meta () in
        let result_ty = Ast.fresh_meta () in
        let result_eff = Ast.fresh_effect () in
        (try
           sub_type fn_ty (TFun (param_ty, result_eff, result_ty));
           sub_type arg_ty param_ty
         with Failure msg ->
           failwith ("Type error in function application: " ^ msg));
        mk result_ty (join [fn_eff; arg_eff; result_eff])
          (FuncApp ((fn_ty, fn_eff, fn_a), (arg_ty, arg_eff, arg_a)))
    | FinConst (k, n) ->
        if k < 0 || k >= n then
          failwith
            (Printf.sprintf
               "Invalid FinConst value: %d#%d. k must be >= 0 and < n."
               k n);
        pure (TFin n) (FinConst (k, n))
    | FinEq (e1, e2, n) ->
        if n <= 0 then
          failwith
            (Printf.sprintf "Invalid FinEq modulus: ==#%d. n must be > 0." n);
        let ((t1, eff1, a1) as te1) = aux env e1 in
        let ((t2, eff2, a2) as te2) = aux env e2 in
        ignore te1;
        ignore te2;
        (try sub_type t1 (TFin n) with
         | Failure msg ->
             failwith
               (Printf.sprintf
                  "Type error in FinEq (==#%d) left operand: %s" n msg));
        (try sub_type t2 (TFin n) with
         | Failure msg ->
             failwith
               (Printf.sprintf
                  "Type error in FinEq (==#%d) right operand: %s" n msg));
        mk TBool (join [eff1; eff2])
          (FinEq ((t1, eff1, a1), (t2, eff2, a2), n))
    | And (e1, e2) -> bool_binary env e1 e2 "And (&&)" (fun a b -> And (a, b))
    | Or (e1, e2) -> bool_binary env e1 e2 "Or (||)" (fun a b -> Or (a, b))
    | Not e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        (try sub_type ty TBool with
         | Failure msg -> failwith ("Type error in Not operand: " ^ msg));
        mk TBool eff (Not (ty, eff, a))
    | Observe e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        (try sub_type ty TBool with
         | Failure msg -> failwith ("Type error in Observe argument: " ^ msg));
        mk TUnit (join [Prob; eff]) (Observe (ty, eff, a))
    | Fix (f, x, body) ->
        let fn_ty = Ast.fresh_meta () in
        let param_ty = Ast.fresh_meta () in
        let env' = StringMap.add x param_ty (StringMap.add f fn_ty env) in
        let ((body_ty, body_eff, _) as typed_body) = aux env' body in
        unify fn_ty (TFun (param_ty, body_eff, body_ty));
        pure fn_ty (Fix (f, x, typed_body))
    | Nil -> pure (TList (Ast.fresh_meta ())) Nil
    | Cons (head, tail) ->
        let ((head_ty, head_eff, head_a) as typed_head) = aux env head in
        let ((tail_ty, tail_eff, tail_a) as typed_tail) = aux env tail in
        ignore typed_head;
        ignore typed_tail;
        (try unify tail_ty (TList head_ty) with
         | Failure msg ->
             failwith ("Type error in list construction (::): " ^ msg));
        mk tail_ty (join [head_eff; tail_eff])
          (Cons ((head_ty, head_eff, head_a), (tail_ty, tail_eff, tail_a)))
    | MatchList (matched, nil_case, head, tail, cons_case) ->
        let ((match_ty, match_eff, match_a) as typed_match) =
          aux env matched
        in
        ignore typed_match;
        let elem_ty = Ast.fresh_meta () in
        (try unify match_ty (TList elem_ty) with
         | Failure msg ->
             failwith
               ("Type error in match expression (expected list type): " ^ msg));
        let ((nil_ty, nil_eff, nil_a) as typed_nil) = aux env nil_case in
        ignore typed_nil;
        let cons_env =
          StringMap.add head elem_ty (StringMap.add tail match_ty env)
        in
        let ((cons_ty, cons_eff, cons_a) as typed_cons) =
          aux cons_env cons_case
        in
        ignore typed_cons;
        let result_ty = Ast.fresh_meta () in
        (try
           sub_type nil_ty result_ty;
           sub_type cons_ty result_ty
         with Failure msg ->
           failwith ("Type error in match branches: " ^ msg));
        mk result_ty (join [match_eff; nil_eff; cons_eff])
          (MatchList
             ( (match_ty, match_eff, match_a)
             , (nil_ty, nil_eff, nil_a)
             , head
             , tail
             , (cons_ty, cons_eff, cons_a) ))
    | Ref e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        mk (TRef ty) eff (Ref (ty, eff, a))
    | Deref e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        let value_ty = Ast.fresh_meta () in
        (try unify ty (TRef value_ty) with
         | Failure msg ->
             failwith ("Type error in dereference (!): " ^ msg));
        mk (Ast.force value_ty) eff (Deref (ty, eff, a))
    | Assign (lhs, rhs) ->
        let ((lhs_ty, lhs_eff, lhs_a) as typed_lhs) = aux env lhs in
        let ((rhs_ty, rhs_eff, rhs_a) as typed_rhs) = aux env rhs in
        ignore typed_lhs;
        ignore typed_rhs;
        let value_ty = Ast.fresh_meta () in
        (try
           unify lhs_ty (TRef value_ty);
           sub_type rhs_ty (Ast.force value_ty)
         with Failure msg ->
           failwith ("Type error in assignment (:=): " ^ msg));
        mk TUnit (join [lhs_eff; rhs_eff])
          (Assign ((lhs_ty, lhs_eff, lhs_a), (rhs_ty, rhs_eff, rhs_a)))
    | Seq (e1, e2) ->
        let ((t1, eff1, a1) as te1) = aux env e1 in
        let ((t2, eff2, a2) as te2) = aux env e2 in
        ignore te1;
        ignore te2;
        mk t2 (join [eff1; eff2])
          (Seq ((t1, eff1, a1), (t2, eff2, a2)))
    | Unit -> pure TUnit Unit
    | RuntimeError msg -> pure (Ast.fresh_meta ()) (RuntimeError msg)
    | Reset e1 ->
        let ((ty, eff, a) as typed) = aux env e1 in
        ignore typed;
        mk ty eff (Reset (ty, eff, a))
    | Shift (k, e1) ->
        let continuation_ty = Ast.fresh_meta () in
        let ((ty, eff, a) as typed) =
          aux (StringMap.add k continuation_ty env) e1
        in
        ignore typed;
        mk ty eff (Shift (k, (ty, eff, a)))

  and arith_aux env e1 e2 rebuild =
    let ((t1, eff1, a1) as te1) = aux env e1 in
    let ((t2, eff2, a2) as te2) = aux env e2 in
    ignore te1;
    ignore te2;
    expect_float t1
      (fun msg -> "Type error in arithmetic left operand: " ^ msg);
    expect_float t2
      (fun msg -> "Type error in arithmetic right operand: " ^ msg);
    mk (fresh_float_ty ()) (join [eff1; eff2])
      (rebuild (t1, eff1, a1) (t2, eff2, a2))

  and bool_binary env e1 e2 name rebuild =
    let ((t1, eff1, a1) as te1) = aux env e1 in
    let ((t2, eff2, a2) as te2) = aux env e2 in
    ignore te1;
    ignore te2;
    (try sub_type t1 TBool with
     | Failure msg ->
         failwith ("Type error in " ^ name ^ " left operand: " ^ msg));
    (try sub_type t2 TBool with
     | Failure msg ->
         failwith ("Type error in " ^ name ^ " right operand: " ^ msg));
    mk TBool (join [eff1; eff2])
      (rebuild (t1, eff1, a1) (t2, eff2, a2))
  in
  aux StringMap.empty e

let infer_bool (e : expr) : typed_expr =
  let ((ty, _, _) as typed) = infer e in
  sub_type ty TBool;
  typed

(* Remove type/effect annotations while preserving the exact expression
   structure.  The cut-analysis pass uses this to replace the general float
   annotations with its cut-aware annotations. *)
let rec erase ((_, _, TAExprNode node) : typed_expr) : expr =
  let expr node = ExprNode node in
  match node with
  | Const f -> expr (Const f)
  | BoolConst b -> expr (BoolConst b)
  | Var x -> expr (Var x)
  | Let (x, e1, e2) -> expr (Let (x, erase e1, erase e2))
  | Sample dist -> expr (Sample (erase_sample dist))
  | DiscreteCase cases ->
      expr (DiscreteCase (List.map (fun (b, p) -> (erase b, erase p)) cases))
  | Cmp (op, e1, e2, flipped) ->
      expr (Cmp (op, erase e1, erase e2, flipped))
  | FinCmp (op, e1, e2, n, flipped) ->
      expr (FinCmp (op, erase e1, erase e2, n, flipped))
  | FinEq (e1, e2, n) -> expr (FinEq (erase e1, erase e2, n))
  | And (e1, e2) -> expr (And (erase e1, erase e2))
  | Or (e1, e2) -> expr (Or (erase e1, erase e2))
  | Not e1 -> expr (Not (erase e1))
  | If (e1, e2, e3) -> expr (If (erase e1, erase e2, erase e3))
  | Pair (e1, e2) -> expr (Pair (erase e1, erase e2))
  | First e1 -> expr (First (erase e1))
  | Second e1 -> expr (Second (erase e1))
  | Fun (x, e1) -> expr (Fun (x, erase e1))
  | FuncApp (e1, e2) -> expr (FuncApp (erase e1, erase e2))
  | Fix (f, x, e1) -> expr (Fix (f, x, erase e1))
  | FinConst (k, n) -> expr (FinConst (k, n))
  | Observe e1 -> expr (Observe (erase e1))
  | Nil -> expr Nil
  | Cons (e1, e2) -> expr (Cons (erase e1, erase e2))
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      expr (MatchList (erase e1, erase e_nil, y, ys, erase e_cons))
  | Ref e1 -> expr (Ref (erase e1))
  | Deref e1 -> expr (Deref (erase e1))
  | Assign (e1, e2) -> expr (Assign (erase e1, erase e2))
  | Seq (e1, e2) -> expr (Seq (erase e1, erase e2))
  | Unit -> expr Unit
  | RuntimeError msg -> expr (RuntimeError msg)
  | Reset e1 -> expr (Reset (erase e1))
  | Shift (k, e1) -> expr (Shift (k, erase e1))
  | Add (e1, e2) -> expr (Add (erase e1, erase e2))
  | Sub (e1, e2) -> expr (Sub (erase e1, erase e2))
  | Mul (e1, e2) -> expr (Mul (erase e1, erase e2))
  | Div (e1, e2) -> expr (Div (erase e1, erase e2))
  | SpecialFunc (name, args) -> expr (SpecialFunc (name, List.map erase args))
  | Cdf (dist, point) -> expr (Cdf (erase_sample dist, erase point))
  | CdfExpr (kernel, point) -> expr (CdfExpr (erase kernel, erase point))

and erase_sample = function
  | Distr1 (kind, e1) -> Distr1 (kind, erase e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, erase e1, erase e2)
