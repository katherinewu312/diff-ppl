open OUnit2
open Slice
module S = Symbolic

let analyze source =
  let expression=Parse.parse_expr source in
  let parameters=Ast.free_variables expression |> Ast.Names.elements
    |> List.map (fun name -> name,S.Parameter name) in
  let solver=Solver.create () in
  let analysis=Execute.run ~solver ~parameters expression in
  Report.check solver analysis

let assert_counts raw retained report =
  assert_equal ~printer:string_of_int raw (List.length report.Report.analysis.candidates);
  assert_equal ~printer:string_of_int retained (List.length (Report.retained report))
let assert_value expected report = assert_equal ~printer:S.to_string expected report.Report.analysis.value
let n i=S.integer i
let lt a b=S.comparison Ast.Lt a b
let sub a b=S.arith Ast.Sub a b
let theta=S.Parameter "theta"
let one_boundary report = match report.Report.analysis.candidates with
  | [b] -> b | _ -> assert_failure "Expected one boundary"
let expect_error source =
  try ignore (analyze source);assert_failure "An unspecified rule must not be silently invented"
  with Execute.Error _ -> ()

let tests = [
  "paper example 1: fixed threshold" >:: (fun _ ->
    let r=analyze "if uniform(0,1)<0.5 then 0 else 1" in
    assert_counts 1 1 r;
    let c=lt (S.Sample 1) (S.number "0.5") in
    assert_value (S.Ite (c,n 0,n 1)) r;
    assert_equal S.truth (one_boundary r).path;
    assert_equal (sub (S.Sample 1) (S.number "0.5")) (one_boundary r).guard);
  "paper example 1: continuous branch boundary dropped" >:: (fun _ ->
    let r=analyze "let x=uniform(0,2) in if x<1 then x else 1" in
    assert_counts 1 0 r);
  "paper example 2: nested conditionals" >:: (fun _ ->
    let r=analyze "if uniform(0,1)<0.5 then theta else if uniform(0,1)<0.8 then theta else theta+1" in
    assert_counts 2 2 r;
    assert_equal 2 (List.length r.analysis.samples);
    let b=List.hd r.analysis.candidates in
    assert_equal (S.negate (lt (S.Sample 1) (S.number "0.5"))) b.path);
  "paper example 3: captured sample and fresh call arguments" >:: (fun _ ->
    let r=analyze "let make=fun t -> fun x -> if x<t then 0 else 1 in let f=make (uniform(0,1)) in f (uniform(0,1))+f (uniform(0,1))" in
    assert_counts 2 2 r;
    assert_equal 3 (List.length r.analysis.samples);
    assert_equal [sub (S.Sample 2) (S.Sample 1);sub (S.Sample 3) (S.Sample 1)]
      (List.map (fun (b:S.boundary) -> b.guard) r.analysis.candidates));
  "paper example 4: recursion reaches base case" >:: (fun _ ->
    let r=analyze "let rec countdown=fun n -> if n<=0 then (if uniform(0,1)<theta then 0 else 1) else countdown (n-1) in countdown 2" in
    assert_counts 1 1 r;
    assert_equal 1 (List.length r.analysis.samples));
  "constant true reachability skips unsupported branch" >:: (fun _ ->
    let r=analyze "if 0.5<0.8 then 0 else observe true" in
    assert_value (n 0) r;assert_counts 0 0 r);
  "let bound false reachability" >:: (fun _ ->
    let r=analyze "let n=10 in if n<0.5 then observe true else 1" in
    assert_value (n 1) r;assert_counts 0 0 r);
  "correlated nested branches use both reachability rules" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in if u<theta then (if u<theta then 1 else 99) else (if u<theta then 99 else 0)" in
    assert_counts 1 1 r;
    assert_value (S.Ite (lt (S.Sample 1) theta,n 1,n 0)) r);
  "different sampling calls do not imply each other's outcome" >:: (fun _ ->
    let r=analyze "if uniform(0,1)<theta then (if uniform(0,1)>=theta then 99 else 1) else 0" in
    assert_counts 2 2 r;
    assert_equal 2 (List.length r.analysis.samples));
  "domain entailment" >:: (fun _ ->
    let r=analyze "if uniform(0,1)<2 then 1 else observe true" in
    assert_value (n 1) r;assert_counts 0 0 r);
  "nonlinear reachability" >:: (fun _ ->
    let r=analyze "let x=gaussian(0,1) in if x*x<0 then observe true else 1" in
    assert_value (n 1) r;assert_counts 0 0 r);
  "uniform affine reparameterization" >:: (fun _ ->
    let r=analyze "uniform(a,b)" in
    assert_value (S.arith Ast.Add (S.Parameter "a")
      (S.arith Ast.Mul (sub (S.Parameter "b") (S.Parameter "a")) (S.Sample 1))) r);
  "Gaussian affine reparameterization" >:: (fun _ ->
    let r=analyze "gaussian(mu,sigma)" in
    assert_value (S.arith Ast.Add (S.Parameter "mu")
      (S.arith Ast.Mul (S.Parameter "sigma") (S.Sample 1))) r;
    assert_equal Ast.Gaussian (List.hd r.analysis.samples).distribution);
  "ordinary closure uses lexical environment" >:: (fun _ ->
    let r=analyze "let a=7 in let f=fun x -> x+a in let a=99 in f 2" in
    assert_value (n 9) r);
  "recursive closure restores self under shadowing" >:: (fun _ ->
    let r=analyze "let rec f=fun n -> if n<=0 then 7 else f (n-1) in let g=f in let f=fun x -> 99 in g 3" in
    assert_value (n 7) r);
  "higher order recursion" >:: (fun _ ->
    let r=analyze "let rec repeat=fun f -> fun n -> fun x -> if n<=0 then x else repeat f (n-1) (f x) in repeat (fun x -> x+1) 3 0" in
    assert_value (n 3) r);
  "recursive list match" >:: (fun _ ->
    let r=analyze "let rec sum=fun xs -> match xs with nil -> 0 | x::rest -> x+sum rest end in sum (1::2::nil)" in
    assert_value (n 3) r);
  "conditional function uses ite application, including original closure candidate" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let f=if u<theta then (fun x -> x+1) else (fun x -> x+2) in f 0" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 1,n 2)) r;
    assert_counts 2 2 r;
    assert_bool "Scalar final outputs do not require extensional closure inequality"
      (List.for_all (fun b -> b.Report.answer=Solver.Sat) r.checked));
  "ite application evaluates the argument once" >:: (fun _ ->
    let r=analyze "let f=if uniform(0,1)<theta then (fun x -> x) else (fun x -> x+1) in f (uniform(0,1))" in
    assert_equal 2 (List.length r.analysis.samples);
    assert_value (S.Ite (lt (S.Sample 1) theta,S.Sample 2,S.arith Ast.Add (S.Sample 2) (n 1))) r);
  "ite application selects entailed true alternative" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let f=if u<theta then (fun x -> x+1) else (fun x -> x+2) in if u<theta then f 0 else 0" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 1,n 0)) r;
    assert_counts 2 2 r);
  "ite application selects entailed false alternative" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let f=if u<theta then (fun x -> x+1) else (fun x -> x+2) in if u<theta then 0 else f 0" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 0,n 2)) r;
    assert_counts 2 2 r);
  "ite application does not execute unreachable unsupported body" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let f=if u<theta then (fun x -> x+1) else (fun x -> observe true) in if u<theta then f 0 else 0" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 1,n 0)) r);
  "ite application does not unfold unreachable recursion" >:: (fun _ ->
    let r=analyze "let rec loop=fun x -> loop x in let u=uniform(0,1) in let f=if u<theta then (fun x -> x+1) else loop in if u<theta then f 0 else 0" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 1,n 0)) r);
  "nested ite application retains unresolved inner alternatives" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let v=uniform(0,1) in let f=if u<theta then (if v<0.5 then (fun x -> 1) else (fun x -> 2)) else (fun x -> 3) in if u<theta then f 0 else 0" in
    assert_value (S.Ite (lt (S.Sample 1) theta,S.Ite (lt (S.Sample 2) (S.number "0.5"),n 1,n 2),n 0)) r);
  "compound predicates record every atom" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in if u<theta && u<0.5 then 0 else 1" in
    assert_counts 2 2 r);
  "Boolean operators use the eager operator rule" >:: (fun _ ->
    let r=analyze "if false && uniform(0,1)<theta then 1 else 0" in
    assert_value (n 0) r;
    assert_equal 1 (List.length r.analysis.samples));
  "negated atom retains Rec's literal branch ordering" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in if not (u<theta) then 1 else 0" in
    let b=one_boundary r in
    assert_equal (sub (S.Sample 1) theta) b.guard;
    assert_equal (n 1) b.minus;assert_equal (n 0) b.plus);
  "finite comparison adds no guard" >:: (fun _ ->
    let r=analyze "fun k -> if k <#2 1#2 then 0 else 1" in
    assert_counts 0 0 r;
    let r=analyze "let f=fun k -> if k <#2 1#2 then 0 else 1 in f 0#2" in
    assert_value (n 0) r);
  "unresolved finite comparison still creates an ite but no guard" >:: (fun _ ->
    let r=analyze "if k <#2 1#2 then 0 else 1" in
    assert_counts 0 0 r;
    assert_value (S.Ite (S.Finite_compare (Ast.Lt,2,S.Parameter "k",S.Finite (1,2)),n 0,n 1)) r);
  "pair projection distributes over ite" >:: (fun _ ->
    let r=analyze "fst (if uniform(0,1)<theta then (1,2) else (3,4))" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 1,n 3)) r;
    assert_counts 2 2 r);
  "list match distributes over ite" >:: (fun _ ->
    let r=analyze "let xs=if uniform(0,1)<theta then nil else 1::nil in match xs with nil -> 0 | x::rest -> x end" in
    assert_value (S.Ite (lt (S.Sample 1) theta,n 0,n 1)) r;
    assert_counts 2 2 r);
  "exact decimal comparisons" >:: (fun _ ->
    let r=analyze "if 0.1+0.2 <= 0.3 then 1 else 0" in
    assert_value (n 1) r;assert_counts 0 0 r);
  "nonlinear joint boundary" >:: (fun _ ->
    let r=analyze "let x=uniform(0,1) in let y=uniform(0,1) in if x*x+y*y<theta then 1 else 0" in
    assert_counts 1 1 r);
  "same guard in side expressions is evaluated one-sided" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let x=if u<theta then 1 else 0 in if x<0.5 then 0 else 1" in
    assert_bool "Candidates are retained without evaluating strict comparisons at the tie"
      (List.length (Report.retained r)>0));
  "boundary query uses one-sided value rather than value at tie" >:: (fun _ ->
    let s=S.Sample 1 in
    let b={S.path=S.truth;guard=sub s theta;minus=S.Ite (lt s theta,n 1,n 0);plus=n 0} in
    let result=Solver.boundary (Solver.create ()) [{S.id=1;distribution=Ast.Uniform}]
      ~value:(S.Ite (lt s theta,n 1,n 0)) b in
    assert_equal Solver.Sat result.answer);
  "boundary query compares symbolic Boolean results" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in if u<theta then u<0.5 else false" in
    assert_counts 1 1 r;
    assert_equal Solver.Sat (List.hd r.checked).answer);
  "comparisons returned directly add no Rec candidate in the written rules" >:: (fun _ ->
    let r=analyze "uniform(0,1)<theta" in assert_counts 0 0 r);
  "Boolean ite used as condition is an explicit grammar gap" >:: (fun _ ->
    expect_error "let b=if uniform(0,1)<theta then true else false in if b then 1 else 0");
  "final-output cancellation drops a local candidate" >:: (fun _ ->
    let r=analyze "let x=if uniform(0,1)<theta then 1 else 0 in x-x" in
    assert_counts 1 0 r;
    let b=List.hd r.checked in
    assert_equal (Some (n 0)) b.minus;assert_equal (Some (n 0)) b.plus);
  "final-output addition doubles the side value" >:: (fun _ ->
    let r=analyze "let x=if uniform(0,1)<theta then 1 else 0 in x+x" in
    assert_counts 1 1 r;
    let b=List.hd r.checked in
    assert_equal (Some (n 2)) b.minus;assert_equal (Some (n 0)) b.plus);
  "subsequent function application transforms the side values" >:: (fun _ ->
    let r=analyze "let x=if uniform(0,1)<theta then 1 else 0 in let f=fun a -> 3*a+2 in f x" in
    assert_counts 1 1 r;
    let b=List.hd r.checked in
    assert_equal (Some (n 5)) b.minus;assert_equal (Some (n 2)) b.plus);
  "equivalent scaled guards cancel in the final output" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let x=if u<theta then 1 else 0 in let y=if 2*u<2*theta then 1 else 0 in x-y" in
    assert_counts 2 0 r);
  "reversed guards are specialized with the opposite orientation" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let x=if u<theta then 1 else 0 in let y=if theta<u then 0 else 1 in x-y" in
    assert_counts 2 0 r);
  "nonlinear sign-equivalent guards cancel" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let g=u-theta in let x=if g<0 then 1 else 0 in let y=if g*g*g<0 then 1 else 0 in x-y" in
    assert_counts 2 0 r);
  "unused local function boundary drops for a constant scalar final output" >:: (fun _ ->
    let r=analyze "let f=if uniform(0,1)<theta then (fun x -> x+1) else (fun x -> x+2) in 0" in
    assert_counts 1 0 r);
  "unresolved final function values remain unknown" >:: (fun _ ->
    let r=analyze "if uniform(0,1)<theta then (fun x -> x+1) else (fun x -> x+2)" in
    assert_counts 1 1 r;
    assert_bool "Function-valued output must not be compared numerically"
      (match (List.hd r.checked).answer with Solver.Unknown _ -> true | _ -> false));
  "local branch ordering under negation does not determine final side orientation" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in if not (u<theta) then 1 else 0" in
    let b=List.hd r.checked in
    assert_equal (Some (n 0)) b.minus;assert_equal (Some (n 1)) b.plus);
  "intersection ambiguity is never treated as proof of continuity" >:: (fun _ ->
    let r=analyze "let u=uniform(0,1) in let x=if u<theta then 1 else 0 in let y=if a*(u-theta)<0 then 1 else 0 in y" in
    let b=List.hd r.checked in
    assert_bool "Unresolved sign changes on a shared surface retain the candidate"
      (match b.answer with Solver.Unknown _ -> true | _ -> false));
  "unsupported source constructs report missing rules" >:: (fun _ ->
    List.iter expect_error ["observe true";"ref 0";"flip(0.5)";"beta(2,3)"]);
  "legacy fix desugars identically" >:: (fun _ ->
    assert_equal (Parse.parse_expr "let f=fix f x := x in f 1")
      (Parse.parse_expr "let rec f=fun x -> x in f 1"));
  "division by zero is not given a symbolic meaning" >:: (fun _ ->
    assert_raises Division_by_zero (fun () -> ignore (analyze "1/0")));
  "negative literals and nested comments" >:: (fun _ ->
    let r=analyze "(* outer (* inner *) *) let x=3 in x-1 + -2" in
    assert_value (n 0) r);
]

let () = run_test_tt_main ("Paper analysis rules" >::: tests)
