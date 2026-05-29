open OUnit2

let transform source =
  let expr = Slice.Parse.parse_expr source in
  let texpr = Slice.Inference.infer expr in
  Slice.Discretization.discretize_top texpr

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

let suite =
  "Slice transformation tests" >:::
  [ "test_typing" >:: test_typing
  ; "test_discretizes_uniform_comparison" >:: test_discretizes_uniform_comparison
  ]

let () = run_test_tt_main suite
