open OUnit2
open Slice
open Execute
module S = Symbolic

let run ?config ?parameters source = Execute.run ?config ?parameters (Parse.parse_expr source)
let returned result = List.filter_map (function Returned (s,v) -> Some (s,v) | _ -> None) result.paths
let assert_complete r = assert_bool (Report.text r) r.complete
let assert_count n r = assert_equal ~printer:string_of_int n (List.length r.paths)
let scalars r = List.map (fun (_,v) -> match v with Scalar t -> t | _ -> assert_failure "Expected scalar") (returned r)
let numeric n = Scalar (S.Number n)
let has_stop predicate r = List.exists (function Stopped (_,why) -> predicate why | _ -> false) r.paths

let tests = [
  "threshold and complementary guards", (fun _ ->
    let r = run "let u=uniform(0,1) in if u<theta then 1 else 0" in
    assert_complete r; assert_count 2 r;
    match returned r with
    | [(a,va);(b,vb)] ->
        assert_equal (numeric 1.) va; assert_equal (numeric 0.) vb;
        assert_equal [S.Binary (S.Lt,S.Sample 0,S.Parameter "theta")] a.constraints;
        assert_equal (List.map S.negate a.constraints) b.constraints;
        assert_equal a.samplings b.samplings
    | _ -> assert_failure "Two returns expected");
  "symbolic discrete thresholds", (fun _ ->
    let r = run "let x=if flip(0.5) then p1 else p2 in let y=uniform(0,1) in y<x" in
    assert_complete r; assert_count 4 r;
    let thresholds = List.concat_map (fun (s,_) -> List.filter_map (function
      | S.Binary (S.Lt,_,S.Parameter p) -> Some p
      | S.Not (S.Binary (S.Lt,_,S.Parameter p)) -> Some p
      | _ -> None) s.constraints) (returned r) in
    assert_equal ["p1";"p2"] (List.sort_uniq compare thresholds));
  "higher order captured threshold", (fun _ ->
    let r = run "let make=fun t -> fun y -> y<t in let f=make theta in f (uniform(0,1))" in
    assert_complete r; assert_count 2 r);
  "branch selected closures", (fun _ ->
    let r = run "let f=if flip(0.5) then (fun x -> x+1) else (fun x -> x+2) in f 3" in
    assert_equal [S.Number 4.;S.Number 5.] (scalars r));
  "lexical scoping", (fun _ ->
    let r = run "let x=1 in let f=fun y -> x+y in let x=100 in f 2" in
    assert_equal [S.Number 3.] (scalars r));
  "shared sample identity", (fun _ ->
    let r = run "let x=uniform(0,1) in (x,x)" in
    match returned r with
    | [(s,Pair_value (Scalar (S.Sample a),Scalar (S.Sample b)))] ->
        assert_equal a b; assert_equal 1 (List.length s.samplings)
    | _ -> assert_failure "Shared sample missing");
  "fresh samples on function calls", (fun _ ->
    let r = run "let f=fun x -> uniform(0,1) in (f (),f ())" in
    match returned r with
    | [(s,Pair_value (Scalar (S.Sample a),Scalar (S.Sample b)))] ->
        assert_bool "Calls must draw fresh samples" (a<>b);
        assert_equal 2 (List.length s.samplings)
    | _ -> assert_failure "Fresh samples missing");
  "correlated branch choices", (fun _ ->
    let r = run "let b=flip(0.5) in let x=if b then 1 else 2 in let y=if b then 2 else 1 in (x,y)" in
    assert_count 2 r;
    assert_equal [Pair_value (numeric 1.,numeric 2.);Pair_value (numeric 2.,numeric 1.)]
      (List.map snd (returned r)));
  "bounded recursive list sum", (fun _ ->
    let r = run "let sum=fix sum xs := match xs with nil -> 0 | x::rest -> x+sum rest end in sum (1::2::nil)" in
    assert_complete r; assert_equal [S.Number 3.] (scalars r));
  "recursion bound retained", (fun _ ->
    let config = {default_config with max_recursion=2} in
    let r = run ~config "let f=fix f x := f x in f 0" in
    assert_bool "Must be incomplete" (not r.complete);
    assert_bool "Limit path retained" (has_stop ((=) Recursion_limit) r));
  "zero recursion bound allows uncalled function", (fun _ ->
    let config={default_config with max_recursion=0} in
    let r=run ~config "let f=fix f x := f x in 7" in
    assert_complete r; assert_equal [S.Number 7.] (scalars r));
  "ordinary higher order divergence step bound", (fun _ ->
    let config={default_config with max_steps=50} in
    let r=run ~config "let f=fun x -> x x in f f" in
    assert_bool "Step exhaustion retained" (has_stop ((=) Step_limit) r));
  "observation acceptance and rejection", (fun _ ->
    let r=run "let u=uniform(0,1) in let ok=observe (u<theta) in 1" in
    assert_complete r; assert_count 2 r;
    assert_equal 1 (List.length (returned r));
    assert_bool "Rejected path retained" (has_stop ((=) Rejected) r);
    List.iter (fun o -> assert_equal 1 (List.length (Report.state o).observations)) r.paths);
  "short circuit has no unwanted draw", (fun _ ->
    let r=run "(false && flip(0.5),true || flip(0.5))" in
    assert_complete r; assert_count 1 r;
    assert_equal [] (Report.state (List.hd r.paths)).samplings);
  "branch local reference stores and aliasing", (fun _ ->
    let r=run "let r=ref 0 in let alias=r in let ignored=(if flip(0.5) then r:=1 else r:=2) in !alias" in
    assert_complete r; assert_equal [S.Number 1.;S.Number 2.] (scalars r));
  "conditional draw appears only on its path", (fun _ ->
    let r=run "if flip(0.5) then uniform(0,1) else 0" in
    assert_equal [2;1] (List.map (fun o -> List.length (Report.state o).samplings) r.paths));
  "dependent sampling kernel", (fun _ ->
    let r=run "let x=uniform(0,1) in gaussian(x,1)" in
    match returned r with
    | [(s,_)] -> (match s.samplings with
        | [_;{kernel=Distribution ("gaussian",[S.Sample 0;S.Number 1.]);_}] -> ()
        | _ -> assert_failure "Conditional kernel lost dependency")
    | _ -> assert_failure "Expected one path");
  "nonlinear joint predicate preserved", (fun _ ->
    let r=run "let x=uniform(0,1) in let y=uniform(0,1) in x*x+y*y<theta" in
    assert_complete r; assert_count 2 r;
    let s=Report.state (List.hd r.paths) in
    assert_equal [0;1] (S.samples (List.hd s.constraints)));
  "identical predicate contradiction pruning", (fun _ ->
    let r=run "let u=uniform(0,1) in if u<theta then (if u<theta then 1 else 99) else 0" in
    assert_count 2 r; assert_equal [S.Number 1.;S.Number 0.] (scalars r));
  "finite discrete syntax", (fun _ ->
    let r=run "let z=discrete(p,1-p) in z ==#2 0#2" in
    assert_complete r; assert_equal [S.Boolean true;S.Boolean false] (scalars r));
  "zero probability branch removed", (fun _ ->
    let r=run "if flip(0) then 99 else 1" in
    assert_count 1 r; assert_equal [S.Number 1.] (scalars r));
  "concrete substitution", (fun _ ->
    let r=run ~parameters:["theta",0.5] "theta+1" in
    assert_equal [S.Number 1.5] (scalars r));
  "runtime error retains sampled prefix", (fun _ ->
    let r=run "let u=uniform(0,1) in 1/0" in
    assert_bool "Runtime error recorded" (has_stop (function Runtime_error _ -> true | _ -> false) r);
    assert_equal 1 (List.length (Report.state (List.hd r.paths)).samplings));
  "invalid probability rejected", (fun _ ->
    let r=run "flip(2)" in
    assert_bool "Invalid probability" (not r.complete));
  "path budget fails rather than returning partial result", (fun _ ->
    let config={default_config with max_paths=1} in
    assert_raises (Path_limit 1) (fun () -> ignore (run ~config "flip(0.5)")));
  "subtraction negative literals and nested comments", (fun _ ->
    let r=run "(* outer\n (* inner *) *) let x=3 in x-1 + -2" in
    assert_equal [S.Number 0.] (scalars r));
  "pair of Boolean queries materialized consistently", (fun _ ->
    let r=run "let x=uniform(0,1) in (x<theta,x<theta)" in
    assert_count 2 r);
  "all named kernels remain representable", (fun _ ->
    List.iter (fun source -> let r=run source in assert_complete r; assert_count 1 r)
      ["uniform(0,1)";"gaussian(0,1)";"normal(0,1)";"exponential(1)";
       "beta(2,3)";"lognormal(0,1)";"gamma(2,1)";"laplace(1)";
       "cauchy(1)";"weibull(1,2)";"tdist(3)";"chi2(3)";
       "logistic(1)";"rayleigh(1)";"pareto(1,2)";"gumbel1(1,2)";
       "gumbel2(1,2)";"exppow(1,2)";"poisson(2)";"binomial(0.5,3)"]);
  "arithmetic and negative kernel parameters", (fun _ ->
    let r=run "gaussian(-theta,1+sigma)" in
    assert_complete r; assert_count 1 r);
  "degenerate uniform is deterministic", (fun _ ->
    let r=run "uniform(0,0)<0" in
    assert_complete r; assert_equal [S.Boolean false] (scalars r));
  "symbolic binomial integrality requirement", (fun _ ->
    let r=run "binomial(p,n)" in
    assert_complete r;
    assert_bool "Trial count must be integral"
      (List.mem (S.Is_integer (S.Parameter "n")) (Report.state (List.hd r.paths)).requirements));
]

let () = run_test_tt_main ("Symbolic operational semantics" >::: List.map (fun (n,f) -> n >:: f) tests)
