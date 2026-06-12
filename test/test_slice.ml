open OUnit2

let transform source =
  let expr = Slice.Parse.parse_expr source in
  let texpr = Slice.Inference.infer expr in
  Slice.Discretization.discretize_top texpr

let adev_gradient source =
  let expr = Slice.Parse.parse_expr source in
  let texpr = Slice.Inference.infer expr in
  Slice.Adev.gradient texpr

let adev_dual_after_discretize source =
  let transformed = transform source in
  let texpr = Slice.Inference.infer transformed in
  Slice.Adev.dual_expectation texpr

let adev_gradient_after_discretize source =
  let transformed = transform source in
  let texpr = Slice.Inference.infer transformed in
  Slice.Adev.gradient texpr

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

let test_typing _ =
  let expr = Slice.Parse.parse_expr "let x = uniform(0, 1) in if x < 0.5 then 0 else 1" in
  let texpr = Slice.Inference.infer expr in
  assert_bool "typed expression should pretty-print" (String.length (Slice.Pretty.string_of_texpr texpr) > 0)

let test_discretizes_uniform_comparison _ =
  let transformed = transform "let x = uniform(0, 1) in x < 0.5" in
  match transformed with
  | Slice.Ast.ExprNode (Let (_, Slice.Ast.ExprNode (Slice.Ast.DistrCase _), _)) -> ()
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

let suite =
  "Slice transformation tests" >:::
  [ "test_typing" >:: test_typing
  ; "test_discretizes_uniform_comparison" >:: test_discretizes_uniform_comparison
  ; "test_adev_enumerates_direct_discrete_comparison" >:: test_adev_enumerates_direct_discrete_comparison
  ; "test_adev_includes_probability_and_body_derivatives" >:: test_adev_includes_probability_and_body_derivatives
  ; "test_adev_uniform_cdf_dual_simplifies" >:: test_adev_uniform_cdf_dual_simplifies
  ; "test_adev_uniform_cdf_gradient_simplifies" >:: test_adev_uniform_cdf_gradient_simplifies
  ]

let () = run_test_tt_main suite
