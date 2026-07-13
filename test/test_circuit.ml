open OUnit2

let infer_with_cuts expression =
  expression
  |> Slice.Inference.infer
  |> Slice.Cut_inference.analyze

let compile_source source =
  let normalized =
    source
    |> Slice.Parse.parse_expr
    |> Slice.Normalize.normalize
  in
  let typed = infer_with_cuts normalized in
  let discretized = Slice.Discretization.discretize_top typed in
  let discretized_typed = infer_with_cuts discretized in
  Slice.Circuit.compile discretized_typed

let assert_close ?(eps = 1e-9) expected actual =
  assert_bool
    (Printf.sprintf "expected %.12g, received %.12g" expected actual)
    (abs_float (expected -. actual) <= eps)

let eval compiled assignments =
  Slice.Circuit.eval compiled assignments

let eval_forward_dual compiled parameter assignments =
  let typed = infer_with_cuts (Slice.Circuit.to_expr compiled) in
  let dual =
    Slice.Forward.dual_expectation
      ~seeds:(Slice.Forward.seeds_of_param parameter)
      typed
  in
  let environment =
    List.map (fun (name, value) -> name, Slice.Ast.VFloat value) assignments
  in
  match Slice.Interp.eval environment dual with
  | Slice.Ast.VPair (Slice.Ast.VFloat primal, Slice.Ast.VFloat tangent) ->
      primal, tangent
  | value ->
      assert_failure
        ("expected a float dual, received " ^ Slice.Ast.string_of_value value)

let eval_reverse_dual compiled parameter assignments =
  let typed = infer_with_cuts (Slice.Circuit.to_expr compiled) in
  let dual =
    Slice.Reverse.dual_expectation
      ~seeds:(Slice.Reverse.seeds_of_param parameter)
      typed
  in
  let environment =
    List.map (fun (name, value) -> name, Slice.Ast.VFloat value) assignments
  in
  match Slice.Interp.eval environment dual with
  | Slice.Ast.VPair (Slice.Ast.VFloat primal, Slice.Ast.VFloat tangent) ->
      primal, tangent
  | value ->
      assert_failure
        ("expected a reverse float dual, received "
         ^ Slice.Ast.string_of_value value)

let rec contains_discrete (Slice.Ast.ExprNode expression) =
  let open Slice.Ast in
  match expression with
  | DiscreteCase _ | Sample _ -> true
  | Const _ | BoolConst _ | Var _ | FinConst _ | Nil | Unit
  | RuntimeError _ -> false
  | Let (_, left, right) | Cmp (_, left, right, _)
  | FinCmp (_, left, right, _, _) | FinEq (left, right, _)
  | And (left, right) | Or (left, right) | Pair (left, right)
  | FuncApp (left, right) | Cons (left, right) | Assign (left, right)
  | Seq (left, right) | Add (left, right) | Sub (left, right)
  | Mul (left, right) | Div (left, right) | CdfExpr (left, right) ->
      contains_discrete left || contains_discrete right
  | Not child | First child | Second child | Observe child | Ref child
  | Deref child | Reset child -> contains_discrete child
  | Shift (_, child) | Fun (_, child) | Fix (_, _, child) ->
      contains_discrete child
  | If (condition, if_true, if_false) ->
      contains_discrete condition
      || contains_discrete if_true
      || contains_discrete if_false
  | MatchList (value, if_nil, _, _, if_cons) ->
      contains_discrete value
      || contains_discrete if_nil
      || contains_discrete if_cons
  | SpecialFunc (_, arguments) -> List.exists contains_discrete arguments
  | Cdf (distribution, point) ->
      contains_discrete_sample distribution || contains_discrete point

and contains_discrete_sample = function
  | Slice.Ast.Distr1 (_, argument) -> contains_discrete argument
  | Slice.Ast.Distr2 (_, left, right) ->
      contains_discrete left || contains_discrete right

let test_arithmetic_hash_consing _ =
  let arithmetic = Slice.Circuit_ir.create () in
  let x = Slice.Circuit_ir.param arithmetic "x" in
  let first = Slice.Circuit_ir.mul arithmetic x x in
  let second = Slice.Circuit_ir.mul arithmetic x x in
  assert_equal first second;
  assert_equal 2 (Slice.Circuit_ir.node_count arithmetic)

let test_decision_hash_consing _ =
  let arithmetic = Slice.Circuit_ir.create () in
  let decisions = Slice.Circuit_dd.create () in
  let x = Slice.Circuit_dd.leaf decisions
      (Slice.Circuit_ir.param arithmetic "x") in
  let y = Slice.Circuit_dd.leaf decisions
      (Slice.Circuit_ir.param arithmetic "y") in
  let variable = Slice.Circuit_dd.fresh_rv decisions ~arity:2 in
  let first = Slice.Circuit_dd.choice decisions variable [| x; y |] in
  let second = Slice.Circuit_dd.choice decisions variable [| x; y |] in
  assert_equal first second;
  assert_equal 3 (Slice.Circuit_dd.node_count decisions)

let test_arithmetic_smart_constructors_preserve_nan _ =
  let arithmetic = Slice.Circuit_ir.create () in
  let zero = Slice.Circuit_ir.const arithmetic 0.0 in
  let x = Slice.Circuit_ir.param arithmetic "x" in
  let zero_over_zero = Slice.Circuit_ir.div arithmetic zero zero in
  let x_over_x = Slice.Circuit_ir.div arithmetic x x in
  let zero_times_x = Slice.Circuit_ir.mul arithmetic zero x in
  let x_minus_x = Slice.Circuit_ir.sub arithmetic x x in
  let eval root assignments =
    Slice.Circuit_runtime.eval arithmetic root assignments
  in
  assert_equal FP_nan (classify_float (eval zero_over_zero []));
  assert_equal FP_nan (classify_float (eval x_over_x [ "x", 0.0 ]));
  assert_equal FP_nan
    (classify_float (eval zero_times_x [ "x", infinity ]));
  assert_equal FP_nan
    (classify_float (eval x_minus_x [ "x", infinity ]))

let test_weighted_branch_compiles_and_differentiates _ =
  let compiled =
    compile_source
      "let z = discrete(p, 1 - p) in \
       if z <#2 1#2 then x + 1 else x * x"
  in
  assert_bool "compiled expression still contains a random choice"
    (not (contains_discrete (Slice.Circuit.to_expr compiled)));
  assert_close 3.75 (eval compiled [ "p", 0.25; "x", 2.0 ]);
  let primal, tangent =
    eval_forward_dual compiled "p" [ "p", 0.25; "x", 2.0 ]
  in
  assert_close 3.75 primal;
  assert_close (-1.0) tangent;
  let reverse_primal, reverse_tangent =
    eval_reverse_dual compiled "p" [ "p", 0.25; "x", 2.0 ]
  in
  assert_close 3.75 reverse_primal;
  assert_close (-1.0) reverse_tangent

let test_shared_choice_preserves_correlation _ =
  let compiled =
    compile_source
      "let z = discrete(p, 1 - p) in \
       let a = if z <#2 1#2 then x else y in \
       a * a"
  in
  assert_close 7.75
    (eval compiled [ "p", 0.25; "x", 2.0; "y", 3.0 ]);
  (* p, x, y, 1, (1-p), x^2, y^2, the two weighted terms, and their sum. *)
  assert_equal 10 compiled.stats.reachable_arithmetic_nodes;
  let _, tangent =
    eval_forward_dual compiled "p"
      [ "p", 0.25; "x", 2.0; "y", 3.0 ]
  in
  assert_close (-5.0) tangent

let test_distinct_choices_are_independent _ =
  let compiled =
    compile_source
      "let z1 = discrete(p, 1 - p) in \
       let z2 = discrete(q, 1 - q) in \
       if z1 <#2 1#2 then \
         if z2 <#2 1#2 then 1.0 else 0.0 \
       else 0.0"
  in
  assert_close 0.1 (eval compiled [ "p", 0.25; "q", 0.4 ])

let test_multivalued_choice _ =
  let compiled =
    compile_source
      "let z = discrete(p, q, 1 - p - q) in \
       if z <#3 1#3 then 10.0 \
       else if z ==#3 1#3 then 20.0 else 30.0"
  in
  assert_close 23.0 (eval compiled [ "p", 0.2; "q", 0.3 ])

let test_boolean_objective_is_indicator _ =
  let compiled =
    compile_source "discrete(p, 1 - p) <#2 1#2"
  in
  assert_close 0.35 (eval compiled [ "p", 0.35 ])

let test_reduction_removes_irrelevant_choices _ =
  let compiled =
    compile_source
      "if discrete(theta, 1 - theta) <#2 1#2 then x1 \
       else if discrete(theta, 1 - theta) <#2 1#2 then x1 else x1"
  in
  (match Slice.Circuit_ir.lookup compiled.arithmetic compiled.root with
   | Slice.Circuit_ir.Param "x1" -> ()
  | _ -> assert_failure "expected the reduced circuit root to be Param(x1)");
  assert_equal 1 compiled.stats.reachable_arithmetic_nodes;
  assert_equal 0 compiled.stats.reachable_random_variables;
  assert_close 4.0 (eval compiled [ "x1", 4.0 ])

let test_additive_maxcut_uses_linearity _ =
  let compiled =
    compile_source
      "let z1 = discrete(p1, 1 - p1) in \
       let z2 = discrete(p2, 1 - p2) in \
       let z3 = discrete(p3, 1 - p3) in \
       let e12 = if z1 ==#2 z2 then 0.0 else 1.0 in \
       let e13 = if z1 ==#2 z3 then 0.0 else 2.0 in \
       let e23 = if z2 ==#2 z3 then 0.0 else 1.5 in \
       e12 + e13 + e23"
  in
  assert_equal 3 compiled.stats.additive_terms;
  assert_close 1.95
    (eval compiled [ "p1", 0.2; "p2", 0.3; "p3", 0.4 ])

let test_subtraction_uses_linearity _ =
  let compiled =
    compile_source
      "let z1 = discrete(p, 1 - p) in \
       let z2 = discrete(q, 1 - q) in \
       let z3 = discrete(r, 1 - r) in \
       let a = if z1 <#2 1#2 then x else y in \
       let b = if z2 <#2 1#2 then u else v in \
       let c = if z3 <#2 1#2 then s else t in \
       a - b - c"
  in
  assert_equal 3 compiled.stats.additive_terms;
  assert_close (-7.0)
    (eval compiled
       [ "p", 0.25; "q", 0.5; "r", 0.75
       ; "x", 2.0; "y", 4.0; "u", 3.0; "v", 5.0
       ; "s", 6.0; "t", 8.0
       ])

let test_constant_conditional_preserves_linearity _ =
  let compiled =
    compile_source
      "let z1 = discrete(p, 1 - p) in \
       let z2 = discrete(q, 1 - q) in \
       if true then \
         (if z1 <#2 1#2 then x else y) + \
         (if z2 <#2 1#2 then u else v) \
       else 0.0"
  in
  assert_equal 2 compiled.stats.additive_terms;
  assert_close 7.7
    (eval compiled
       [ "p", 0.25; "q", 0.4
       ; "x", 2.0; "y", 4.0; "u", 3.0; "v", 5.0
       ])

let test_rejects_residual_sample _ =
  assert_raises
    (Failure
       "Circuit compilation: residual Sample is not supported by the initial circuit backend")
    (fun () -> ignore (compile_source "uniform(0, 1)"))

let test_rejects_observe _ =
  assert_raises
    (Failure
       "Circuit compilation: Observe is not supported by the initial circuit backend")
    (fun () ->
       ignore
         (compile_source "let ignored = observe(true) in 1.0"))

let suite =
  "Circuit compiler tests" >::: 
  [ "arithmetic hash-consing" >:: test_arithmetic_hash_consing
  ; "decision hash-consing" >:: test_decision_hash_consing
  ; "smart constructors preserve NaN" >:: test_arithmetic_smart_constructors_preserve_nan
  ; "weighted branch and AD" >:: test_weighted_branch_compiles_and_differentiates
  ; "shared choice correlation" >:: test_shared_choice_preserves_correlation
  ; "distinct choices independent" >:: test_distinct_choices_are_independent
  ; "multivalued choice" >:: test_multivalued_choice
  ; "boolean objective" >:: test_boolean_objective_is_indicator
  ; "irrelevant choices reduce" >:: test_reduction_removes_irrelevant_choices
  ; "additive MaxCut linearity" >:: test_additive_maxcut_uses_linearity
  ; "subtraction linearity" >:: test_subtraction_uses_linearity
  ; "constant conditional linearity" >:: test_constant_conditional_preserves_linearity
  ; "reject residual Sample" >:: test_rejects_residual_sample
  ; "reject Observe" >:: test_rejects_observe
  ]

let () = run_test_tt_main suite
