(* Type inference and elaboration for continuous dice *)

open Ast
open Lats

module StringMap = Map.Make(String)

(* Pretty-print an [expr] to a canonical string with no ANSI color
   codes.  Used as the identity for entries in [SymSet]. *)
let canonical_string_of_expr (e : expr) : string =
  Pretty.string_of_expr_plain e

(* Helper to construct a sym-bag containing a single symbolic
   expression. *)
let singleton_sym_bag (e : expr) : SymLat.bag =
  let s = canonical_string_of_expr e in
  SymLat.create (Finite (SymSet.singleton (s, e)))

(* Enforce t_sub is a subtype of t_super *)
let rec sub_type (t_sub : ty) (t_super : ty) : unit =
  match Ast.force t_sub, Ast.force t_super with
  (* Base Cases *)
  | TBool,    TBool      -> ()
  | TFin n1, TFin n2 when n1 = n2 -> ()
  | TUnit, TUnit -> ()
  (* Structural Cases *)
  | TFloat (b1, c1, s1), TFloat (b2, c2, s2) ->
      Ast.CutLat.eq b1 b2;     (* Cuts must agree *)
      Lats.FloatLat.leq c1 c2; (* Concrete constants flow sub -> super *)
      Ast.SymLat.leq s1 s2     (* Symbolic values flow sub -> super *)
  | TPair(a1, b1), TPair(a2, b2) ->
      sub_type a1 a2;
      sub_type b1 b2
  | TFun(a1, eff1, b1), TFun(a2, eff2, b2) ->
      sub_type a2 a1;
      Ast.effect_leq eff1 eff2;
      sub_type b1 b2
  | TList t1, TList t2 -> sub_type t1 t2
  | TRef t1, TRef t2 -> unify t1 t2
  | TMeta r, _ ->
    (match Ast.force t_super with
    | TMeta r' -> (Ast.listen r (fun t -> sub_type t t_super); Ast.listen r' (fun t' -> sub_type t_sub t'))
    | TBool -> Ast.assign r TBool
    | TFin n -> Ast.assign r (TFin n)
    | TPair (_, _) -> let a_meta = Ast.fresh_meta () in let b_meta = Ast.fresh_meta () in
      Ast.assign r (TPair (a_meta, b_meta)); sub_type t_sub t_super
    | TFun (_, _, _) -> let a_meta = Ast.fresh_meta () in let b_meta = Ast.fresh_meta () in
      Ast.assign r (TFun (a_meta, Ast.fresh_effect (), b_meta)); sub_type t_sub t_super
    | TFloat (_, _, _) ->
      let b_bag = Ast.fresh_cut_bag () in
      let c_bag = Lats.fresh_float_bag () in
      let s_bag = Ast.fresh_sym_bag () in
      Ast.assign r (TFloat (b_bag, c_bag, s_bag)); sub_type t_sub t_super
    | TUnit -> Ast.assign r TUnit
    | TList _ -> let elem_meta = Ast.fresh_meta () in
                 Ast.assign r (TList elem_meta); sub_type t_sub t_super
    | TRef _ -> let ref_meta = Ast.fresh_meta () in
                Ast.assign r (TRef ref_meta); sub_type t_sub t_super
    )
  | _, TMeta r ->
    (match Ast.force t_sub with
    | TMeta r' -> (Ast.listen r (fun t -> sub_type t_sub t); Ast.listen r' (fun t' -> sub_type t_sub t'))
    | TBool -> Ast.assign r TBool
    | TFin n -> Ast.assign r (TFin n)
    | TPair (_, _) -> let a_meta = Ast.fresh_meta () in let b_meta = Ast.fresh_meta () in
      Ast.assign r (TPair (a_meta, b_meta)); sub_type t_sub t_super
    | TFun (_, _, _) -> let a_meta = Ast.fresh_meta () in let b_meta = Ast.fresh_meta () in
      Ast.assign r (TFun (a_meta, Ast.fresh_effect (), b_meta)); sub_type t_sub t_super
    | TFloat (_, _, _) ->
      let b_bag = Ast.fresh_cut_bag () in
      let c_bag = Lats.fresh_float_bag () in
      let s_bag = Ast.fresh_sym_bag () in
      Ast.assign r (TFloat (b_bag, c_bag, s_bag)); sub_type t_sub t_super
    | TUnit -> Ast.assign r TUnit
    | TList _ -> let elem_meta = Ast.fresh_meta () in
                 Ast.assign r (TList elem_meta); sub_type t_sub t_super
    | TRef _ -> let ref_meta = Ast.fresh_meta () in
                Ast.assign r (TRef ref_meta); sub_type t_sub t_super
    )
  (* Error Case *)
  | _, _ ->
      let msg = Printf.sprintf "Type mismatch: cannot subtype %s <: %s"
        (Pretty.string_of_ty t_sub) (Pretty.string_of_ty t_super)
      in
      failwith msg

and unify (t1 : ty) (t2 : ty) : unit =
  try
    sub_type t1 t2;
    sub_type t2 t1
  with Failure msg ->
    let unified_msg = Printf.sprintf "Type mismatch: cannot unify %s and %s\n(Subtyping error: %s)"
      (Pretty.string_of_ty t1) (Pretty.string_of_ty t2) msg
    in
    failwith unified_msg

(* Construct a fresh TFloat for an arithmetic result whose value is
   represented by the symbolic expression [orig_expr] (the original
   surface-syntax form). *)
let arith_result_ty (orig_expr : expr) : ty =
  let cuts_bag = Ast.fresh_cut_bag () in
  let floats_bag = Lats.fresh_float_bag () in (* empty: value is symbolic *)
  let sym_bag = singleton_sym_bag orig_expr in
  TFloat (cuts_bag, floats_bag, sym_bag)

(* Add a single symbolic-expression cut to a cut bag (only if the
   bag is currently finite and the cut is not already present). *)
let add_sym_cut_to_bag (b_meta : Ast.CutLat.bag) (cuts : Ast.CutSet.t) : unit =
  match Ast.CutLat.get b_meta with
  | Top -> ()
  | Finite current ->
    let merged = Ast.CutSet.union current cuts in
    if not (Ast.CutSet.equal current merged) then
      let temp = Ast.CutLat.create (Finite merged) in
      Ast.CutLat.leq temp b_meta

(* Build a symbolic cut value from an expr.  Falls back to constant
   when the expr is a [Const]. *)
let sym_cut_val_of_expr (e : expr) : cut_val =
  match e with
  | ExprNode (Const f) -> CVConst f
  | _ -> CVSym (canonical_string_of_expr e, e)

(* Type inference and elaboration: expr -> texpr *)
let infer (e : expr) : texpr =
  let mk ty eff ae = (ty, eff, TAExprNode ae) in
  let pure ty ae = mk ty Pure ae in
  let prob ty ae = mk ty Prob ae in
  let ty_of (ty, _, _) = ty in
  let eff_of (_, eff, _) = eff in
  let join = Ast.join_effects in
  let rec aux (env : ty StringMap.t) (orig_expr : expr) : texpr =
    let ExprNode e_node = orig_expr in
    match e_node with
    | Const f ->
      let cuts_bag_ref = Ast.CutLat.create (Finite Ast.CutSet.empty) in
      let consts_bag_ref = Lats.FloatLat.create (Finite (FloatSet.singleton f)) in
      let sym_bag_ref = Ast.SymLat.create (Finite Ast.SymSet.empty) in
      pure (TFloat (cuts_bag_ref, consts_bag_ref, sym_bag_ref)) (Const f)
    | BoolConst b ->
      pure TBool (BoolConst b)
    | Var x ->
      (try
        let ty = StringMap.find x env in
        pure ty (Var x)
       with Not_found ->
        (* Free variables are treated as symbolic floats whose only
           reachable value is the variable itself. *)
        let cuts_bag = Ast.fresh_cut_bag () in
        let floats_bag = Lats.fresh_float_bag () in
        let sym_bag = singleton_sym_bag (ExprNode (Var x)) in
        pure (TFloat (cuts_bag, floats_bag, sym_bag)) (Var x))

    | Let (x, e1, e2) ->
      let t1, eff1, a1 = aux env e1 in
      let env' = StringMap.add x t1 env in
      let t2, eff2, a2 = aux env' e2 in
      mk t2 (join [eff1; eff2]) (Let (x, (t1, eff1, a1), (t2, eff2, a2)))

    | Add (e1, e2) -> arith_aux env orig_expr e1 e2 "Add" (fun a b -> Add (a, b))
    | Sub (e1, e2) -> arith_aux env orig_expr e1 e2 "Sub" (fun a b -> Sub (a, b))
    | Mul (e1, e2) -> arith_aux env orig_expr e1 e2 "Mul" (fun a b -> Mul (a, b))
    | Div (e1, e2) -> arith_aux env orig_expr e1 e2 "Div" (fun a b -> Div (a, b))

    | SpecialFunc (name, args) ->
      let typed_args =
        List.map
          (fun e ->
             let t, eff, a = aux env e in
             let arg_cut = Ast.fresh_cut_bag () in
             let arg_float = Lats.fresh_float_bag () in
             let arg_sym = Ast.fresh_sym_bag () in
             (try sub_type t (TFloat (arg_cut, arg_float, arg_sym))
              with Failure msg ->
                failwith ("Type error in special function " ^ name ^ ": " ^ msg));
             (t, eff, a))
          args
      in
      let cuts_bag = Ast.fresh_cut_bag () in
      let floats_bag = Lats.fresh_float_bag () in
      let sym_bag = singleton_sym_bag orig_expr in
      mk (TFloat (cuts_bag, floats_bag, sym_bag))
        (join (List.map eff_of typed_args))
        (SpecialFunc (name, typed_args))

    | Cdf (dist_exp, point_e) ->
      (* CDF nodes are emitted by the discretizer and may be consumed
         by later source-to-source passes, so preserve their shape in
         the typed AST instead of replacing them with a dummy const. *)
      let infer_cdf_arg e arg_name =
        let t, eff, a = aux env e in
        let arg_cut = Ast.fresh_cut_bag () in
        let arg_float = Lats.fresh_float_bag () in
        let arg_sym = Ast.fresh_sym_bag () in
        (try sub_type t (TFloat (arg_cut, arg_float, arg_sym))
         with Failure msg -> failwith ("Type error in CDF " ^ arg_name ^ ": " ^ msg));
        (t, eff, a)
      in
      let dist_exp' =
        match dist_exp with
        | Distr1 (kind, e1) ->
            let te1 = infer_cdf_arg e1 "distribution argument" in
            Distr1 (kind, te1)
        | Distr2 (kind, e1, e2) ->
            let te1 = infer_cdf_arg e1 "first distribution argument" in
            let te2 = infer_cdf_arg e2 "second distribution argument" in
            Distr2 (kind, te1, te2)
      in
      let point_te = infer_cdf_arg point_e "point argument" in
      let cuts_bag = Ast.fresh_cut_bag () in
      let floats_bag = Lats.fresh_float_bag () in
      let sym_bag = singleton_sym_bag orig_expr in
      let dist_eff =
        match dist_exp' with
        | Distr1 (_, te1) -> eff_of te1
        | Distr2 (_, te1, te2) -> join [eff_of te1; eff_of te2]
      in
      mk (TFloat (cuts_bag, floats_bag, sym_bag))
        (join [dist_eff; eff_of point_te])
        (Cdf (dist_exp', point_te))

    | CdfExpr (kernel_e, point_e) ->
      let infer_float e arg_name =
        let t, eff, a = aux env e in
        let arg_cut = Ast.fresh_cut_bag () in
        let arg_float = Lats.fresh_float_bag () in
        let arg_sym = Ast.fresh_sym_bag () in
        (try sub_type t (TFloat (arg_cut, arg_float, arg_sym))
         with Failure msg -> failwith ("Type error in CDF expression " ^ arg_name ^ ": " ^ msg));
        (t, eff, a)
      in
      let kernel_te = infer_float kernel_e "kernel argument" in
      let point_te = infer_float point_e "point argument" in
      let cuts_bag = Ast.fresh_cut_bag () in
      let floats_bag = Lats.fresh_float_bag () in
      let sym_bag = singleton_sym_bag orig_expr in
      mk (TFloat (cuts_bag, floats_bag, sym_bag))
        (join [eff_of kernel_te; eff_of point_te])
        (CdfExpr (kernel_te, point_te))

    | Sample dist_exp ->
      let cuts_bag_ref = Ast.CutLat.create (Finite Ast.CutSet.empty) in
      let consts_bag_ref = Lats.FloatLat.create Top in
      let sym_bag_ref = Ast.SymLat.create (Finite Ast.SymSet.empty) in

      let add_floats_to_cutbag (float_bag : FloatLat.bag) (cut_bag : Ast.CutLat.bag) =
        let listener () =
          let v = Lats.FloatLat.get float_bag in
          (match v with
          | Finite s -> Ast.CutLat.add_all s cut_bag
            | Top -> Ast.CutLat.leq (Ast.CutLat.create Top) cut_bag)
        in
        Lats.FloatLat.listen float_bag listener
      in

      let make_output_top_if_input_boundbag_is_top input_cut_bag =
        let listener () =
          let v = Ast.CutLat.get input_cut_bag in
          (match v with
          | Top -> Ast.CutLat.leq (Ast.CutLat.create Top) cuts_bag_ref
          | _ -> ())
        in
        Ast.CutLat.listen input_cut_bag listener
      in

      let make_input_top_if_output_boundbag_is_top input_cut_bag output_cut_bag =
        let listener () =
          let v = Ast.CutLat.get output_cut_bag in
          (match v with
          | Top -> Ast.CutLat.leq (Ast.CutLat.create Top) input_cut_bag
          | _ -> ())
        in
        Ast.CutLat.listen output_cut_bag listener
      in

      (match dist_exp with
      | Distr1 (dist_kind, arg_e) ->
          let t_arg, eff_arg, a_arg = aux env arg_e in
          let t_arg_cut_bag = Ast.fresh_cut_bag () in
          let t_arg_float_bag = Lats.fresh_float_bag () in
          let t_arg_sym_bag = Ast.fresh_sym_bag () in
          (try unify t_arg (Ast.TFloat (t_arg_cut_bag, t_arg_float_bag, t_arg_sym_bag))
           with Failure msg ->
            let kind_str = Pretty.string_of_expr_indented (ExprNode (Sample (Distr1 (dist_kind, arg_e)))) in
            failwith (Printf.sprintf "Type error in Sample (%s) argument: %s" kind_str msg));

          add_floats_to_cutbag t_arg_float_bag t_arg_cut_bag;
          make_output_top_if_input_boundbag_is_top t_arg_cut_bag;
          make_input_top_if_output_boundbag_is_top t_arg_cut_bag cuts_bag_ref;

          let dist_exp' = Distr1 (dist_kind, (t_arg, eff_arg, a_arg)) in
          prob (TFloat (cuts_bag_ref, consts_bag_ref, sym_bag_ref)) (Sample dist_exp')

      | Distr2 (dist_kind, arg1_e, arg2_e) ->
        let t1, eff1, a1 = aux env arg1_e in
        let t2, eff2, a2 = aux env arg2_e in
        let t1_cut_bag = Ast.fresh_cut_bag () in
        let t1_float_bag = Lats.fresh_float_bag () in
        let t1_sym_bag = Ast.fresh_sym_bag () in
        let t2_cut_bag = Ast.fresh_cut_bag () in
        let t2_float_bag = Lats.fresh_float_bag () in
        let t2_sym_bag = Ast.fresh_sym_bag () in

        (try unify t1 (Ast.TFloat (t1_cut_bag, t1_float_bag, t1_sym_bag))
         with Failure msg ->
          let kind_str = Pretty.string_of_expr_indented (ExprNode (Sample (Distr2 (dist_kind, arg1_e, arg2_e)))) in
          failwith (Printf.sprintf "Type error in Sample (%s) first argument: %s" kind_str msg));
        (try unify t2 (Ast.TFloat (t2_cut_bag, t2_float_bag, t2_sym_bag))
         with Failure msg ->
          let kind_str = Pretty.string_of_expr_indented (ExprNode (Sample (Distr2 (dist_kind, arg1_e, arg2_e)))) in
          failwith (Printf.sprintf "Type error in Sample (%s) second argument: %s" kind_str msg));

        add_floats_to_cutbag t1_float_bag t1_cut_bag;
        add_floats_to_cutbag t2_float_bag t2_cut_bag;

        make_output_top_if_input_boundbag_is_top t1_cut_bag;
        make_output_top_if_input_boundbag_is_top t2_cut_bag;

        make_input_top_if_output_boundbag_is_top t1_cut_bag cuts_bag_ref;
        make_input_top_if_output_boundbag_is_top t2_cut_bag cuts_bag_ref;

        let dist_exp' = Distr2 (dist_kind, (t1, eff1, a1), (t2, eff2, a2)) in
        prob (TFloat (cuts_bag_ref, consts_bag_ref, sym_bag_ref)) (Sample dist_exp')
      )

    | DiscreteCase cases ->
      if cases = [] then failwith "DiscreteCase cannot be empty";
      (* Type-check probability expressions (must be float) and
         branch expressions; subtype branches into a fresh result. *)
      let result_ty = Ast.fresh_meta () in
      let typed_cases = List.map (fun (branch, prob) ->
        let tb, effb, ab = aux env branch in
        (try sub_type tb result_ty
         with Failure msg -> failwith ("Type error in DiscreteCase branches: " ^ msg));
        let tp, effp, ap = aux env prob in
        (* Probability must be a float (concrete or symbolic).
           We don't check sum-to-one when probabilities are
           symbolic. *)
        let pf_cuts = Ast.fresh_cut_bag () in
        let pf_floats = Lats.fresh_float_bag () in
        let pf_sym = Ast.fresh_sym_bag () in
        (try sub_type tp (TFloat (pf_cuts, pf_floats, pf_sym))
         with Failure msg -> failwith ("Type error in DiscreteCase probability: " ^ msg));
        ((tb, effb, ab), (tp, effp, ap))
      ) cases in
      prob result_ty (DiscreteCase typed_cases)

    | Cmp (cmp_op, e1, e2, flipped) ->
        let t1, eff1, a1 = aux env e1 in
        let t2, eff2, a2 = aux env e2 in
        let b_meta = Ast.fresh_cut_bag () in
        let c_meta1 = Lats.fresh_float_bag () in
        let c_meta2 = Lats.fresh_float_bag () in
        let s_meta1 = Ast.fresh_sym_bag () in
        let s_meta2 = Ast.fresh_sym_bag () in
        (try unify t1 (Ast.TFloat (b_meta, c_meta1, s_meta1))
         with Failure msg -> failwith (Printf.sprintf "Type error in comparison left operand: %s" msg));
        (try unify t2 (Ast.TFloat (b_meta, c_meta2, s_meta2))
         with Failure msg -> failwith (Printf.sprintf "Type error in comparison right operand: %s" msg));

        (* Listener: when either side's float bag or sym bag
           changes, recompute the cuts contributed by both sides
           and add them to the shared bound bag. *)
        let listener () =
          let v1 = Lats.FloatLat.get c_meta1 in
          let v2 = Lats.FloatLat.get c_meta2 in
          let sv1 = Ast.SymLat.get s_meta1 in
          let sv2 = Ast.SymLat.get s_meta2 in
          let any_top = (v1 = Top) || (v2 = Top) in
          let both_finite_constants = (not any_top) && (sv1 = Finite Ast.SymSet.empty) && (sv2 = Finite Ast.SymSet.empty) in
          match v1, v2 with
          | Top, Top when sv1 = Finite Ast.SymSet.empty && sv2 = Finite Ast.SymSet.empty ->
              (* Both totally unknown -> BoundBag becomes Top *)
              Ast.CutLat.leq (Ast.CutLat.create Top) b_meta
          | _ when both_finite_constants ->
              (* Both sides are finite sets of concrete constants.
                 This is the "discrete-vs-discrete" case from the
                 original code: only collect cuts from the right
                 bag, treated as the constant. *)
              (match v2 with
               | Finite s2 ->
                 let cuts_to_add = ref Ast.CutSet.empty in
                 FloatSet.iter (fun f ->
                   let cv = CVConst f in
                   let cut = match cmp_op with
                     | Ast.Lt -> Less cv
                     | Ast.Le -> LessEq cv
                   in
                   cuts_to_add := Ast.CutSet.add cut !cuts_to_add
                 ) s2;
                 add_sym_cut_to_bag b_meta !cuts_to_add
               | Top -> ())
          | _ ->
              (* The general "continuous-vs-continuous" or
                 "continuous-vs-symbolic-or-constant" case:
                 collect cuts from both sides (with appropriate
                 op flipping for the LHS). *)
              let cuts_to_add = ref Ast.CutSet.empty in

              (* RHS contributions: concrete floats and symbolic
                 values are added with the original op. *)
              (match v2 with
               | Finite s2 ->
                   FloatSet.iter (fun f ->
                     let cut = match cmp_op with
                       | Ast.Lt -> Less (CVConst f)
                       | Ast.Le -> LessEq (CVConst f)
                     in
                     cuts_to_add := Ast.CutSet.add cut !cuts_to_add
                   ) s2
               | Top -> ());
              (match sv2 with
               | Finite ss2 ->
                   Ast.SymSet.iter (fun (_, e) ->
                     (* Skip symbolic values that themselves
                        contain a Sample: they aren't usable as
                        cut points (their value depends on
                        randomness). *)
                     if not (Normalize.contains_sample e) then
                       let cv = sym_cut_val_of_expr e in
                       let cut = match cmp_op with
                         | Ast.Lt -> Less cv
                         | Ast.Le -> LessEq cv
                       in
                       cuts_to_add := Ast.CutSet.add cut !cuts_to_add
                   ) ss2
               | Top -> ());

              (* LHS contributions: same floats/syms but with the
                 dual operator (e1 < f iff not (f <= e1)). *)
              (match v1 with
               | Finite s1 ->
                   FloatSet.iter (fun f ->
                     let cut = match cmp_op with
                       | Ast.Lt -> LessEq (CVConst f)
                       | Ast.Le -> Less (CVConst f)
                     in
                     cuts_to_add := Ast.CutSet.add cut !cuts_to_add
                   ) s1
               | Top -> ());
              (match sv1 with
               | Finite ss1 ->
                   Ast.SymSet.iter (fun (_, e) ->
                     if not (Normalize.contains_sample e) then
                       let cv = sym_cut_val_of_expr e in
                       let cut = match cmp_op with
                         | Ast.Lt -> LessEq cv
                         | Ast.Le -> Less cv
                       in
                       cuts_to_add := Ast.CutSet.add cut !cuts_to_add
                   ) ss1
               | Top -> ());

              if not (Ast.CutSet.is_empty !cuts_to_add) then
                add_sym_cut_to_bag b_meta !cuts_to_add
        in
        Lats.FloatLat.listen c_meta1 listener;
        Lats.FloatLat.listen c_meta2 listener;
        Ast.SymLat.listen s_meta1 listener;
        Ast.SymLat.listen s_meta2 listener;

        mk TBool (join [eff1; eff2])
          (Cmp (cmp_op, (t1, eff1, a1), (t2, eff2, a2), flipped))

    | FinCmp (cmp_op, e1, e2, n, flipped) ->
      if n <= 0 then failwith (Printf.sprintf "Invalid FinCmp modulus: ==#%d. n must be > 0." n);
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      let expected_type = Ast.TFin n in
      (try sub_type t1 expected_type
       with Failure msg -> failwith (Printf.sprintf "Type error in FinCmp (==#%d) left operand: %s" n msg));
      (try sub_type t2 expected_type
       with Failure msg -> failwith (Printf.sprintf "Type error in FinCmp (==#%d) right operand: %s" n msg));
      mk Ast.TBool (join [eff1; eff2])
        (FinCmp (cmp_op, (t1, eff1, a1), (t2, eff2, a2), n, flipped))

    | If (e1, e2, e3) ->
      let t1, eff1, a1 = aux env e1 in
      (try sub_type t1 Ast.TBool
       with Failure msg -> failwith ("Type error in If condition: " ^ msg));
      let t2, eff2, a2 = aux env e2 in
      let t3, eff3, a3 = aux env e3 in
      let result_ty = Ast.fresh_meta () in
      (try
         sub_type t2 result_ty;
         sub_type t3 result_ty
       with Failure msg -> failwith ("Type error in If branches: " ^ msg));
      mk result_ty (join [eff1; eff2; eff3])
        (If ((t1, eff1, a1), (t2, eff2, a2), (t3, eff3, a3)))

    | Pair (e1, e2) ->
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      mk (TPair (t1, t2)) (join [eff1; eff2])
        (Pair ((t1, eff1, a1), (t2, eff2, a2)))

    | First e1 ->
      let t, eff, a = aux env e1 in
      let t1_meta = Ast.fresh_meta () in
      let t2_meta = Ast.fresh_meta () in
      (try sub_type t (TPair (t1_meta, t2_meta))
       with Failure msg -> failwith ("Type error in First (fst): " ^ msg));
      mk (Ast.force t1_meta) eff (First (t, eff, a))

    | Second e1 ->
      let t, eff, a = aux env e1 in
      let t1_meta = Ast.fresh_meta () in
      let t2_meta = Ast.fresh_meta () in
      (try sub_type t (TPair (t1_meta, t2_meta))
       with Failure msg -> failwith ("Type error in Second (snd): " ^ msg));
      mk (Ast.force t2_meta) eff (Second (t, eff, a))

    | Fun (x, e1) ->
      let param_type = Ast.fresh_meta () in
      let env' = StringMap.add x param_type env in
      let return_type, return_eff, a = aux env' e1 in
      pure (Ast.TFun (param_type, return_eff, return_type))
        (Fun (x, (return_type, return_eff, a)))

    | FuncApp (e1, e2) ->
      let t_fun, eff_fun, a_fun = aux env e1 in
      let t_arg, eff_arg, a_arg = aux env e2 in
      let param_ty_expected = Ast.fresh_meta () in
      let result_ty = Ast.fresh_meta () in
      let result_eff = Ast.fresh_effect () in
      (try
         sub_type t_fun (Ast.TFun (param_ty_expected, result_eff, result_ty));
         sub_type t_arg param_ty_expected
       with Failure msg -> failwith ("Type error in function application: " ^ msg));
      mk result_ty (join [eff_fun; eff_arg; result_eff])
        (FuncApp ((t_fun, eff_fun, a_fun), (t_arg, eff_arg, a_arg)))

    | FinConst (k, n) ->
      if k < 0 || k >= n then failwith (Printf.sprintf "Invalid FinConst value: %d#%d. k must be >= 0 and < n." k n);
      pure (Ast.TFin n) (FinConst (k, n))

    | FinEq (e1, e2, n) ->
      if n <= 0 then failwith (Printf.sprintf "Invalid FinEq modulus: ==#%d. n must be > 0." n);
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      let expected_type = Ast.TFin n in
      (try sub_type t1 expected_type
       with Failure msg -> failwith (Printf.sprintf "Type error in FinEq (==#%d) left operand: %s" n msg));
      (try sub_type t2 expected_type
       with Failure msg -> failwith (Printf.sprintf "Type error in FinEq (==#%d) right operand: %s" n msg));
      mk Ast.TBool (join [eff1; eff2])
        (FinEq ((t1, eff1, a1), (t2, eff2, a2), n))

    | And (e1, e2) ->
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      (try sub_type t1 Ast.TBool
       with Failure msg -> failwith ("Type error in And (&&) left operand: " ^ msg));
      (try sub_type t2 Ast.TBool
       with Failure msg -> failwith ("Type error in And (&&) right operand: " ^ msg));
      mk TBool (join [eff1; eff2]) (And ((t1, eff1, a1), (t2, eff2, a2)))

    | Or (e1, e2) ->
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      (try sub_type t1 Ast.TBool
       with Failure msg -> failwith ("Type error in Or (||) left operand: " ^ msg));
      (try sub_type t2 Ast.TBool
       with Failure msg -> failwith ("Type error in Or (||) right operand: " ^ msg));
      mk TBool (join [eff1; eff2]) (Or ((t1, eff1, a1), (t2, eff2, a2)))

    | Not e1 ->
      let t1, eff1, a1 = aux env e1 in
      (try sub_type t1 Ast.TBool
       with Failure msg -> failwith ("Type error in Not operand: " ^ msg));
      mk TBool eff1 (Not (t1, eff1, a1))

    | Observe e1 ->
      let t1, eff1, a1 = aux env e1 in
      (try sub_type t1 TBool
       with Failure msg -> failwith ("Type error in Observe argument: " ^ msg));
      mk TUnit (join [Prob; eff1]) (Observe (t1, eff1, a1))

    | Fix (f, x, e_body) ->
      let fun_type_itself = Ast.fresh_meta () in
      let param_type = Ast.fresh_meta () in
      let env_body = StringMap.add x param_type (StringMap.add f fun_type_itself env) in
      let body_texpr = aux env_body e_body in
      let body_ret_type = ty_of body_texpr in
      let body_eff = eff_of body_texpr in
      let actual_fun_type = Ast.TFun (param_type, body_eff, body_ret_type) in
      unify fun_type_itself actual_fun_type;
      pure fun_type_itself (Fix (f, x, body_texpr))

    | Nil ->
      let elem_ty = Ast.fresh_meta () in
      pure (TList elem_ty) Nil

    | Cons (e_hd, e_tl) ->
      let t_hd, eff_hd, a_hd = aux env e_hd in
      let t_tl, eff_tl, a_tl = aux env e_tl in
      (try unify t_tl (TList t_hd)
       with Failure msg -> failwith ("Type error in list construction (::): " ^ msg));
      mk t_tl (join [eff_hd; eff_tl])
        (Cons ((t_hd, eff_hd, a_hd), (t_tl, eff_tl, a_tl)))

    | MatchList (e_match, e_nil, y, ys, e_cons) ->
      let t_match, eff_match, a_match = aux env e_match in
      let elem_ty = Ast.fresh_meta () in
      (try unify t_match (TList elem_ty)
       with Failure msg -> failwith ("Type error in match expression (expected list type): " ^ msg));
      let t_nil, eff_nil, a_nil = aux env e_nil in
      let env_cons = StringMap.add y elem_ty (StringMap.add ys t_match env) in
      let t_cons, eff_cons, a_cons = aux env_cons e_cons in
      let result_ty = Ast.fresh_meta () in
      (try
         sub_type t_nil result_ty;
         sub_type t_cons result_ty
       with Failure msg -> failwith ("Type error in match branches: " ^ msg));
      mk result_ty (join [eff_match; eff_nil; eff_cons])
        (MatchList
           ((t_match, eff_match, a_match), (t_nil, eff_nil, a_nil), y, ys,
            (t_cons, eff_cons, a_cons)))

    | Ref e1 ->
      let t1, eff1, a1 = aux env e1 in
      mk (TRef t1) eff1 (Ref (t1, eff1, a1))

    | Deref e1 ->
      let t1, eff1, a1 = aux env e1 in
      let val_ty = Ast.fresh_meta () in
      (try unify t1 (TRef val_ty)
       with Failure msg -> failwith ("Type error in dereference (!): " ^ msg));
      mk (Ast.force val_ty) eff1 (Deref (t1, eff1, a1))

    | Assign (e1, e2) ->
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      let val_ty = Ast.fresh_meta () in
      (try
         unify t1 (TRef val_ty);
         sub_type t2 (Ast.force val_ty)
       with Failure msg -> failwith ("Type error in assignment (:=): " ^ msg));
      mk TUnit (join [eff1; eff2]) (Assign ((t1, eff1, a1), (t2, eff2, a2)))

    | Seq (e1, e2) ->
      let t1, eff1, a1 = aux env e1 in
      let t2, eff2, a2 = aux env e2 in
      mk t2 (join [eff1; eff2]) (Seq ((t1, eff1, a1), (t2, eff2, a2)))

    | Unit -> pure Ast.TUnit Unit

    | RuntimeError s -> pure (Ast.fresh_meta ()) (RuntimeError s)

    | Reset e1 ->
      let t1, eff1, a1 = aux env e1 in
      mk t1 eff1 (Reset (t1, eff1, a1))

    | Shift (k, e1) ->
      let cont_type = Ast.fresh_meta () in
      let env' = StringMap.add k cont_type env in
      let t1, eff1, a1 = aux env' e1 in
      mk t1 eff1 (Shift (k, (t1, eff1, a1)))

  (* Inference for an arithmetic operation; the result's type is a
     fresh symbolic float whose sym-bag identifies the whole
     [orig_expr]. *)
  and arith_aux env orig_expr e1 e2 _op_name rebuild =
    let t1, eff1, a1 = aux env e1 in
    let t2, eff2, a2 = aux env e2 in
    (* Both operands must be floats. *)
    let dummy_cut1 = Ast.fresh_cut_bag () in
    let dummy_float1 = Lats.fresh_float_bag () in
    let dummy_sym1 = Ast.fresh_sym_bag () in
    let dummy_cut2 = Ast.fresh_cut_bag () in
    let dummy_float2 = Lats.fresh_float_bag () in
    let dummy_sym2 = Ast.fresh_sym_bag () in
    (try sub_type t1 (TFloat (dummy_cut1, dummy_float1, dummy_sym1))
     with Failure msg -> failwith ("Type error in arithmetic left operand: " ^ msg));
    (try sub_type t2 (TFloat (dummy_cut2, dummy_float2, dummy_sym2))
     with Failure msg -> failwith ("Type error in arithmetic right operand: " ^ msg));
    let result_ty = arith_result_ty orig_expr in
    mk result_ty (join [eff1; eff2])
      (rebuild (t1, eff1, a1) (t2, eff2, a2))

  in
  aux StringMap.empty e

let infer_bool (e : expr) : texpr =
  let t, eff, a = infer e in
  sub_type t Ast.TBool;
  (t, eff, a)
