open OUnit2

let transform source =
  let expr = Slice.Parse.parse_expr source in
  let texpr = Slice.Inference.infer expr in
  Slice.Discretization.discretize_top texpr

let transform_at param value source =
  let expr = Slice.Parse.parse_expr source in
  let texpr = Slice.Inference.infer expr in
  let cut_order_at : Slice.Cut_order.at =
    { Slice.Cut_order.param = param; value }
  in
  Slice.Discretization.discretize_top ~cut_order_at texpr

let adev_gradient source =
  let expr = Slice.Parse.parse_expr source in
  let texpr = Slice.Inference.infer expr in
  Slice.Adev.gradient texpr

let adev_dual_after_discretize source =
  let transformed = transform source in
  let texpr = Slice.Inference.infer transformed in
  Slice.Adev.dual_expectation texpr

let adev_dual_raw_after_discretize source =
  let transformed = transform source in
  let texpr = Slice.Inference.infer transformed in
  Slice.Adev.dual_expectation_raw texpr

let adev_dual_after_discretize_at param value source =
  let transformed = transform_at param value source in
  let texpr = Slice.Inference.infer transformed in
  let raw = Slice.Adev.dual_expectation_raw ~param texpr in
  let simplified = Slice.Adev.dual_expectation ~param texpr in
  ( Slice.Simplify.subst_float param value raw
  , Slice.Simplify.algebraic (Slice.Simplify.subst_float param value simplified) )

let adev_gradient_after_discretize source =
  let transformed = transform source in
  let texpr = Slice.Inference.infer transformed in
  Slice.Adev.gradient texpr

let adev_dual_with_seeds seeds source =
  let transformed = transform source in
  let texpr = Slice.Inference.infer transformed in
  Slice.Adev.dual_expectation ~seeds texpr

let seeds assignments =
  List.fold_left
    (fun acc (name, value) -> Slice.Adev.add_seed name value acc)
    Slice.Adev.no_seeds
    assignments

let contains_substring s needle =
  let len = String.length s in
  let n = String.length needle in
  let rec loop i =
    i + n <= len && (String.sub s i n = needle || loop (i + 1))
  in
  n = 0 || loop 0

let eval_float_with_theta theta expr =
  match Slice.Interp.eval [("theta", Slice.Ast.VFloat theta)] expr with
  | Slice.Ast.VFloat f -> f
  | v ->
      assert_failure
        ("expected float result, got: " ^ Slice.Ast.string_of_value v)

let eval_dual_with_theta theta expr =
  match Slice.Interp.eval [("theta", Slice.Ast.VFloat theta)] expr with
  | Slice.Ast.VPair (Slice.Ast.VFloat primal, Slice.Ast.VFloat tangent) ->
      (primal, tangent)
  | v ->
      assert_failure
        ("expected dual float pair, got: " ^ Slice.Ast.string_of_value v)

let eval_dual_with_env env expr =
  match Slice.Interp.eval env expr with
  | Slice.Ast.VPair (Slice.Ast.VFloat primal, Slice.Ast.VFloat tangent) ->
      (primal, tangent)
  | v ->
      assert_failure
        ("expected dual float pair, got: " ^ Slice.Ast.string_of_value v)

let assert_prob_effect eff =
  match Slice.Ast.force_effect eff with
  | Slice.Ast.Prob -> ()
  | Slice.Ast.Pure | Slice.Ast.EMeta _ ->
      assert_failure "expected probabilistic effect"

let assert_pure_effect eff =
  match Slice.Ast.force_effect eff with
  | Slice.Ast.Pure -> ()
  | Slice.Ast.Prob | Slice.Ast.EMeta _ ->
      assert_failure "expected pure effect"

let assert_const_dual expected_primal expected_tangent expr =
  match expr with
  | Slice.Ast.ExprNode
      (Slice.Ast.Pair
         (Slice.Ast.ExprNode (Slice.Ast.Const primal),
          Slice.Ast.ExprNode (Slice.Ast.Const tangent))) ->
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        expected_primal
        primal;
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        expected_tangent
        tangent
  | e ->
      assert_failure
        ("expected constant dual pair, got: "
         ^ Slice.Pretty.string_of_expr_plain e)

let cdf_point = function
  | Slice.Ast.ExprNode (Slice.Ast.Cdf (_, point))
  | Slice.Ast.ExprNode (Slice.Ast.CdfExpr (_, point)) -> Some point
  | _ -> None

let right_cdf_point = function
  | Slice.Ast.ExprNode (Slice.Ast.Sub (right_cdf, _)) -> cdf_point right_cdf
  | _ -> None

let generated_distribution_cut_points transformed =
  match transformed with
  | Slice.Ast.ExprNode
      (Slice.Ast.Let (_, Slice.Ast.ExprNode (Slice.Ast.DiscreteCase cases), _)) ->
      List.filter_map right_cdf_point (List.map snd cases)
  | _ ->
      assert_failure
        ("expected top-level let-bound discrete case, got: "
         ^ Slice.Pretty.string_of_expr_plain transformed)

let fin_cmp_rhs_index = function
  | Slice.Ast.ExprNode
      (Slice.Ast.FinCmp
         (_, _, Slice.Ast.ExprNode (Slice.Ast.FinConst (k, n)), _, _)) ->
      (k, n)
  | e ->
      assert_failure
        ("expected finite comparison against finite constant, got: "
         ^ Slice.Pretty.string_of_expr_plain e)

let assert_nested_cut_indices expected_outer expected_inner transformed =
  match transformed with
  | Slice.Ast.ExprNode
      (Slice.Ast.Let
         ( _
         , Slice.Ast.ExprNode (Slice.Ast.DiscreteCase _)
         , Slice.Ast.ExprNode
             (Slice.Ast.If
                ( outer_cmp
                , Slice.Ast.ExprNode (Slice.Ast.If (inner_cmp, _, _))
                , _ )))) ->
      assert_equal expected_outer (fin_cmp_rhs_index outer_cmp);
      assert_equal expected_inner (fin_cmp_rhs_index inner_cmp)
  | _ ->
      assert_failure
        ("expected nested finite comparisons, got: "
         ^ Slice.Pretty.string_of_expr_plain transformed)

let test_typing _ =
  let expr = Slice.Parse.parse_expr "let x = uniform(0, 1) in if x < 0.5 then 0 else 1" in
  let texpr = Slice.Inference.infer expr in
  assert_bool "typed expression should pretty-print" (String.length (Slice.Pretty.string_of_texpr texpr) > 0)

let test_discretizes_uniform_comparison _ =
  let transformed = transform "let x = uniform(0, 1) in x < 0.5" in
  match transformed with
  | Slice.Ast.ExprNode (Let (_, Slice.Ast.ExprNode (Slice.Ast.DiscreteCase _), _)) -> ()
  | _ ->
      assert_failure
        ("expected uniform comparison to discretize to a discrete case, got: "
        ^ Slice.Pretty.string_of_expr transformed)

let test_adev_enumerates_direct_discrete_comparison _ =
  let grad = adev_gradient "discrete(theta, 1 - theta) <#2 1#2" in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    1.0
    (eval_float_with_theta 0.3 grad)

let test_adev_includes_probability_and_body_derivatives _ =
  let grad =
    adev_gradient
      "let x = discrete(theta, 1 - theta) in if x <#2 1#2 then theta else 0"
  in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.6
    (eval_float_with_theta 0.3 grad)

let test_adev_uniform_cdf_dual_simplifies _ =
  let dual = adev_dual_after_discretize "uniform(0, 1) < theta" in
  let primal, tangent = eval_dual_with_theta 0.3 dual in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.3
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    1.0
    tangent

let test_adev_uniform_cdf_gradient_simplifies _ =
  let grad = adev_gradient_after_discretize "uniform(0, 1) < theta" in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    1.0
    (eval_float_with_theta 0.3 grad)

let test_adev_gaussian_cdf_dual_simplifies _ =
  let raw = adev_dual_raw_after_discretize "gaussian(0, 1) < theta" in
  assert_bool "raw gaussian CDF AD should expose an erf closed form"
    (contains_substring (Slice.Pretty.string_of_expr_plain raw) "erf(");
  let dual = adev_dual_after_discretize "gaussian(0, 1) < theta" in
  let primal, tangent = eval_dual_with_theta 0.0 dual in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.5
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.3989422804014327
    tangent

let test_adev_beta_cdf_dual_simplifies_at _ =
  let raw = adev_dual_raw_after_discretize "beta(2, 3) < theta" in
  assert_bool "raw beta CDF AD should expose a beta_inc closed form"
    (contains_substring (Slice.Pretty.string_of_expr_plain raw) "beta_inc(");
  let _, simplified =
    adev_dual_after_discretize_at "theta" 0.4 "beta(2, 3) < theta"
  in
  match simplified with
  | Slice.Ast.ExprNode
      (Slice.Ast.Pair
         (Slice.Ast.ExprNode (Slice.Ast.Const primal),
          Slice.Ast.ExprNode (Slice.Ast.Const tangent))) ->
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        0.5248
        primal;
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        1.728
        tangent
  | _ ->
      assert_failure
        ("expected beta AD-at output to be a constant dual pair, got: "
         ^ Slice.Pretty.string_of_expr_plain simplified)

let test_adev_dual_at_substitutes_raw_and_simplifies _ =
  let raw, simplified =
    adev_dual_after_discretize_at "theta" 0.3 "uniform(0, 1) < theta"
  in
  let raw_plain = Slice.Pretty.string_of_expr_plain raw in
  assert_bool "raw AD program should contain the concrete parameter value"
    (contains_substring raw_plain "0.3");
  assert_bool "raw AD program should not contain the substituted parameter"
    (not (contains_substring raw_plain "theta"));
  (match simplified with
   | Slice.Ast.ExprNode
       (Slice.Ast.Pair
          (Slice.Ast.ExprNode (Slice.Ast.Const primal),
           Slice.Ast.ExprNode (Slice.Ast.Const tangent))) ->
       assert_equal
         ~printer:string_of_float
         ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
         0.3
         primal;
       assert_equal
         ~printer:string_of_float
         ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
         1.0
         tangent
   | _ ->
       assert_failure
         ("expected simplified AD-at output to be a constant dual pair, got: "
          ^ Slice.Pretty.string_of_expr_plain simplified))

let test_adev_dual_at_can_use_non_theta_parameter _ =
  let _, simplified =
    adev_dual_after_discretize_at "alpha" 0.4 "uniform(0, 1) < alpha"
  in
  match simplified with
  | Slice.Ast.ExprNode
      (Slice.Ast.Pair
         (Slice.Ast.ExprNode (Slice.Ast.Const primal),
          Slice.Ast.ExprNode (Slice.Ast.Const tangent))) ->
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        0.4
        primal;
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        1.0
        tangent
  | _ ->
      assert_failure
        ("expected non-theta AD-at output to be a constant dual pair, got: "
         ^ Slice.Pretty.string_of_expr_plain simplified)

let test_adev_infers_single_non_theta_seed _ =
  let expr = Slice.Parse.parse_expr "foo * foo" in
  let texpr = Slice.Inference.infer expr in
  let dual = Slice.Adev.dual_expectation texpr in
  let primal, tangent = eval_dual_with_env ["foo", Slice.Ast.VFloat 0.4] dual in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.16
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.8
    tangent

let test_adev_requires_seed_for_multiple_free_float_variables _ =
  let expr = Slice.Parse.parse_expr "foo + bar" in
  let texpr = Slice.Inference.infer expr in
  assert_raises
    (Failure "ADEV: multiple free float variables found (bar, foo); please specify at least one dVARIABLE seed, e.g. dbar=1")
    (fun () -> ignore (Slice.Adev.dual_expectation texpr))

let test_adev_allows_one_seed_for_multiple_free_float_variables _ =
  let expr = Slice.Parse.parse_expr "foo + bar" in
  let texpr = Slice.Inference.infer expr in
  let dual = Slice.Adev.dual_expectation ~seeds:(seeds ["foo", 1.0]) texpr in
  let primal, tangent =
    eval_dual_with_env
      [ "foo", Slice.Ast.VFloat 0.4
      ; "bar", Slice.Ast.VFloat 0.3
      ]
      dual
  in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.7
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    1.0
    tangent

let test_adev_explicit_seed_for_non_theta_variable _ =
  let dual =
    adev_dual_with_seeds
      (seeds ["alpha", 1.0])
      "alpha * alpha + theta"
  in
  let primal, tangent =
    eval_dual_with_env
      [ "alpha", Slice.Ast.VFloat 0.4
      ; "theta", Slice.Ast.VFloat 0.3
      ]
      dual
  in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.46
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.8
    tangent

let test_reverse_multiple_explicit_unit_seeds _ =
  let expr = Slice.Parse.parse_expr "theta * alpha" in
  let texpr = Slice.Inference.infer expr in
  let dual =
    Slice.Reverse.dual_expectation
      ~seeds:(seeds ["theta", 1.0; "alpha", 1.0])
      texpr
  in
  let primal, tangent =
    eval_dual_with_env
      [ "theta", Slice.Ast.VFloat 0.3
      ; "alpha", Slice.Ast.VFloat 0.4
      ]
      dual
  in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.12
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.7
    tangent

let test_adev_multiple_explicit_unit_seeds _ =
  let dual =
    adev_dual_with_seeds
      (seeds ["theta", 1.0; "alpha", 1.0])
      "theta * alpha"
  in
  let primal, tangent =
    eval_dual_with_env
      [ "theta", Slice.Ast.VFloat 0.3
      ; "alpha", Slice.Ast.VFloat 0.4
      ]
      dual
  in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.12
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.7
    tangent

let test_adev_dual_simplifies_polynomial_components _ =
  let source =
    "if discrete(theta, 1 - theta) <#2 1#2 then theta else theta + 1"
  in
  let raw = adev_dual_raw_after_discretize source in
  let raw_plain = Slice.Pretty.string_of_expr_plain raw in
  assert_bool "raw AD program should still expose fst projections"
    (contains_substring raw_plain "fst");
  assert_bool "raw AD program should still expose snd projections"
    (contains_substring raw_plain "snd");
  match adev_dual_after_discretize source with
  | Slice.Ast.ExprNode
      (Slice.Ast.Pair
         (Slice.Ast.ExprNode (Slice.Ast.Const primal),
          Slice.Ast.ExprNode (Slice.Ast.Const tangent))) ->
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        1.0
        primal;
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        0.0
        tangent
  | e ->
      assert_failure
        ("expected simplified AD dual to be (1, 0), got: "
         ^ Slice.Pretty.string_of_expr_plain e)

let test_probabilistic_function_effect_inference _ =
  let texpr =
    Slice.Inference.infer
      (Slice.Parse.parse_expr "fun x -> discrete(x, 1 - x)")
  in
  match texpr with
  | Slice.Ast.TFun (_, ret_eff, ret_ty), expr_eff, _ ->
      assert_pure_effect expr_eff;
      assert_prob_effect ret_eff;
      (match Slice.Ast.force ret_ty with
       | Slice.Ast.TFin 2 -> ()
       | ty ->
           assert_failure
             ("expected probabilistic function to return #2, got: "
              ^ Slice.Pretty.string_of_ty ty))
  | ty, _, _ ->
      assert_failure
        ("expected probabilistic function type, got: "
         ^ Slice.Pretty.string_of_ty ty)

let test_adev_probabilistic_function_application _ =
  let source =
    "let f = fun x -> discrete(x, 1 - x) in if f theta <#2 1#2 then theta else 0"
  in
  let raw_plain =
    Slice.Pretty.string_of_expr_plain (adev_dual_raw_after_discretize source)
  in
  assert_bool "raw probabilistic function should be continuation-passing"
    (contains_substring raw_plain "_adev_k");
  let primal, tangent = eval_dual_with_theta 0.3 (adev_dual_after_discretize source) in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.09
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.6
    tangent

let test_adev_probabilistic_function_application_simplifies_at _ =
  let source =
    "let f = fun x -> discrete(x, 1 - x) in if f theta <#2 1#2 then theta else 0"
  in
  let _, simplified = adev_dual_after_discretize_at "theta" 0.5 source in
  match simplified with
  | Slice.Ast.ExprNode
      (Slice.Ast.Pair
         (Slice.Ast.ExprNode (Slice.Ast.Const primal),
          Slice.Ast.ExprNode (Slice.Ast.Const tangent))) ->
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        0.25
        primal;
      assert_equal
        ~printer:string_of_float
        ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
        1.0
        tangent
  | e ->
      assert_failure
        ("expected simplified higher-order AD output to be (0.25, 1), got: "
         ^ Slice.Pretty.string_of_expr_plain e)

let test_adev_higher_order_probabilistic_function_application _ =
  let source =
    "let apply = fun f -> f theta in \
     let pf = fun x -> discrete(x, 1 - x) in \
     if apply pf <#2 1#2 then theta else 0"
  in
  let primal, tangent = eval_dual_with_theta 0.3 (adev_dual_after_discretize source) in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.09
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.6
    tangent

let test_adev_probabilistic_fix_loop_application _ =
  let source =
    "let choose = fix choose x := discrete(x, 1 - x) in \
     if choose theta <#2 1#2 then theta else 0"
  in
  let raw_plain =
    Slice.Pretty.string_of_expr_plain (adev_dual_raw_after_discretize source)
  in
  assert_bool "raw probabilistic fix should be continuation-passing"
    (contains_substring raw_plain "_adev_k");
  let primal, tangent = eval_dual_with_theta 0.3 (adev_dual_after_discretize source) in
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.09
    primal;
  assert_equal
    ~printer:string_of_float
    ~cmp:(fun a b -> abs_float (a -. b) < 1e-9)
    0.6
    tangent

let test_adev_probabilistic_fix_loop_application_simplifies_at _ =
  let source =
    "let choose = fix choose x := discrete(x, 1 - x) in \
     if choose theta <#2 1#2 then theta else 0"
  in
  let _, simplified = adev_dual_after_discretize_at "theta" 0.5 source in
  assert_const_dual 0.25 1.0 simplified

let test_adev_list_match_simplifies_at _ =
  let source =
    "match theta :: nil with \
     | nil -> 0 \
     | x :: xs -> x * x \
     end"
  in
  let _, simplified = adev_dual_after_discretize_at "theta" 0.5 source in
  assert_const_dual 0.25 1.0 simplified

let test_adev_recursive_list_sum_simplifies_at _ =
  let source =
    "let sum = fix sum xs := \
       match xs with \
       | nil -> 0 \
       | y :: ys -> y + sum ys \
       end \
     in \
     sum (theta :: ((theta + 1) :: nil))"
  in
  let _, simplified = adev_dual_after_discretize_at "theta" 0.5 source in
  assert_const_dual 2.0 2.0 simplified

let test_discretize_at_orders_theta_squared_before_theta _ =
  let transformed =
    transform_at "theta" 0.5
      "let x = uniform(0, 1) in if x < theta then if x < theta * theta then 1 else 2 else 3"
  in
  let points =
    List.map Slice.Pretty.string_of_expr_plain
      (generated_distribution_cut_points transformed)
  in
  assert_equal
    ~printer:(String.concat "; ")
    ["(theta * theta)"; "theta"]
    points;
  assert_nested_cut_indices (2, 3) (1, 3) transformed

let test_discretize_at_orders_theta_before_theta_plus_one _ =
  let transformed =
    transform_at "theta" 0.5
      "let x = uniform(0, 1) in if x < theta then if x < theta + 1 then 1 else 2 else 3"
  in
  let points =
    List.map Slice.Pretty.string_of_expr_plain
      (generated_distribution_cut_points transformed)
  in
  assert_equal
    ~printer:(String.concat "; ")
    ["theta"; "(theta + 1)"]
    points;
  assert_nested_cut_indices (1, 3) (2, 3) transformed

let suite =
  "Slice transformation tests" >:::
  [ "test_typing" >:: test_typing
  ; "test_discretizes_uniform_comparison" >:: test_discretizes_uniform_comparison
  ; "test_adev_enumerates_direct_discrete_comparison" >:: test_adev_enumerates_direct_discrete_comparison
  ; "test_adev_includes_probability_and_body_derivatives" >:: test_adev_includes_probability_and_body_derivatives
  ; "test_adev_uniform_cdf_dual_simplifies" >:: test_adev_uniform_cdf_dual_simplifies
  ; "test_adev_uniform_cdf_gradient_simplifies" >:: test_adev_uniform_cdf_gradient_simplifies
  ; "test_adev_gaussian_cdf_dual_simplifies" >:: test_adev_gaussian_cdf_dual_simplifies
  ; "test_adev_beta_cdf_dual_simplifies_at" >:: test_adev_beta_cdf_dual_simplifies_at
  ; "test_adev_dual_at_substitutes_raw_and_simplifies" >:: test_adev_dual_at_substitutes_raw_and_simplifies
  ; "test_adev_dual_at_can_use_non_theta_parameter" >:: test_adev_dual_at_can_use_non_theta_parameter
  ; "test_adev_infers_single_non_theta_seed" >:: test_adev_infers_single_non_theta_seed
  ; "test_adev_requires_seed_for_multiple_free_float_variables" >:: test_adev_requires_seed_for_multiple_free_float_variables
  ; "test_adev_allows_one_seed_for_multiple_free_float_variables" >:: test_adev_allows_one_seed_for_multiple_free_float_variables
  ; "test_adev_explicit_seed_for_non_theta_variable" >:: test_adev_explicit_seed_for_non_theta_variable
  ; "test_reverse_multiple_explicit_unit_seeds" >:: test_reverse_multiple_explicit_unit_seeds
  ; "test_adev_multiple_explicit_unit_seeds" >:: test_adev_multiple_explicit_unit_seeds
  ; "test_adev_dual_simplifies_polynomial_components" >:: test_adev_dual_simplifies_polynomial_components
  ; "test_probabilistic_function_effect_inference" >:: test_probabilistic_function_effect_inference
  ; "test_adev_probabilistic_function_application" >:: test_adev_probabilistic_function_application
  ; "test_adev_probabilistic_function_application_simplifies_at" >:: test_adev_probabilistic_function_application_simplifies_at
  ; "test_adev_higher_order_probabilistic_function_application" >:: test_adev_higher_order_probabilistic_function_application
  ; "test_adev_probabilistic_fix_loop_application" >:: test_adev_probabilistic_fix_loop_application
  ; "test_adev_probabilistic_fix_loop_application_simplifies_at" >:: test_adev_probabilistic_fix_loop_application_simplifies_at
  ; "test_adev_list_match_simplifies_at" >:: test_adev_list_match_simplifies_at
  ; "test_adev_recursive_list_sum_simplifies_at" >:: test_adev_recursive_list_sum_simplifies_at
  ; "test_discretize_at_orders_theta_squared_before_theta" >:: test_discretize_at_orders_theta_squared_before_theta
  ; "test_discretize_at_orders_theta_before_theta_plus_one" >:: test_discretize_at_orders_theta_before_theta_plus_one
  ]

let () = run_test_tt_main suite
