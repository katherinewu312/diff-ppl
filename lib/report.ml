module S = Symbolic

type checked = {
  boundary : S.boundary;
  minus : S.t option;
  plus : S.t option;
  answer : Solver.answer;
  exceptional_conditions : S.t list;
  trace_region : S.t option;
  integration_region : S.t option;
}
type t = { analysis : Execute.result; refined_value : S.t; checked : checked list }

let retained_answer = function
  | Solver.Unsat | Solver.Redundant _ -> false
  | Solver.Sat | Solver.Unknown _ -> true

let check solver analysis =
  let samples=analysis.Execute.samples in
  let normalization=Solver.normalize_final solver samples analysis.value in
  let refined_value=normalization.normalized_value in
  let covered=ref S.falsity in
  let checked=List.map (fun boundary ->
    let item=if Solver.globally_eliminated normalization boundary then
      let side=if Solver.polynomial refined_value then Some refined_value else None in
      {boundary;minus=side;plus=side;exceptional_conditions=[];
       trace_region=None;integration_region=None;
       answer=Solver.Redundant "Guard eliminated from the complete symbolic output"}
    else
      let result=Solver.boundary solver samples ~candidates:analysis.candidates
        ~covered:!covered ~value:refined_value boundary in
      {boundary;minus=result.minus;plus=result.plus;answer=result.answer;
       exceptional_conditions=result.exceptional_conditions;
       trace_region=result.trace_region;integration_region=result.integration_region} in
    (* Give each retained surface portion to its first certified representative.
       Exact exclusion also handles coincidence at exceptional parameter values.
       The regular regions omit only certified negligible intersections, so the
       union of these scopes is covered almost everywhere, on every fiber.
       UNKNOWN records never justify dropping another record. *)
    (match item.answer with
     | Solver.Sat -> covered:=S.or_ !covered
         (S.and_ (Solver.relaxed_path boundary.path) (Solver.equal_zero boundary.guard))
     | _ -> ());
    item) analysis.candidates in
  {analysis;refined_value;checked}

let retained report = List.filter (fun b -> retained_answer b.answer) report.checked
let tuple (b:S.boundary) = Printf.sprintf "(%s; %s; %s; %s)"
  (S.to_string b.path) (S.to_string b.guard)
  (S.to_string b.minus) (S.to_string b.plus)

let text report =
  let buffer=Buffer.create 1024 in
  let line fmt=Printf.bprintf buffer (fmt ^^ "\n") in
  line "Symbolic value: %s" (S.to_string report.analysis.value);
  line "Refined symbolic value: %s" (S.to_string report.refined_value);
  line "\nBase samples:";
  List.iter (fun (s:S.sample) -> line "  s%d ~ %s" s.id
    (match s.distribution with
     | Ast.Uniform -> "Uniform(0, 1), 0 < s < 1"
     | Gaussian -> "Gaussian(0, 1), s in R")) report.analysis.samples;
  line "\nCandidate boundaries B: %d" (List.length report.checked);
  line "  (path; guard; v_minus; v_plus), as recorded by Rec";
  List.iteri (fun i b ->
    line "  %d. %s" (i+1) (tuple b.boundary);
    (match b.minus,b.plus with
     | Some minus,Some plus -> line "     one-sided output limits: %s ; %s"
         (S.to_string minus) (S.to_string plus)
     | _ -> line "     final-output sides: not required or unresolved");
    List.iter (fun e -> line "     possible coincidence condition: %s"
      (S.to_string e)) b.exceptional_conditions;
    line "     %s: %s" (Solver.status b.answer) (match b.answer with
      | Solver.Unsat -> "dropped (zero jump almost everywhere)"
      | Solver.Redundant reason -> "dropped (" ^ reason ^ ")"
      | Solver.Sat -> "retained (certified jump at a regular point)"
      | Solver.Unknown reason -> "retained (" ^ reason ^ ")")) report.checked;
  let boundaries=retained report in
  line "\nRetained boundaries B*: %d" (List.length boundaries);
  if boundaries=[] then line "  (none)";
  List.iteri (fun i b ->
    line "  %d. %s = 0 [%s]" (i+1)
      (S.to_string b.boundary.guard) (Solver.status b.answer);
    line "     path: %s" (S.to_string b.boundary.path);
    (match b.minus,b.plus with
     | Some minus,Some plus ->
         line "     output limit from g < 0: %s" (S.to_string minus);
         line "     output limit from g > 0: %s" (S.to_string plus)
     | _ -> line "     final-output sides: unresolved");
    List.iter (fun e -> line "     possible coincidence condition: %s"
      (S.to_string e)) b.exceptional_conditions;
    match b.answer with
    | Solver.Unknown reason -> line "     unconfirmed candidate: %s" reason
    | _ -> ()) boundaries;
  let count predicate=List.length (List.filter (fun x -> predicate x.answer) report.checked) in
  line "\nSummary: SAT %d, UNSAT %d, REDUNDANT %d, UNKNOWN %d"
    (count (function Solver.Sat -> true | _ -> false))
    (count (function Solver.Unsat -> true | _ -> false))
    (count (function Solver.Redundant _ -> true | _ -> false))
    (count (function Solver.Unknown _ -> true | _ -> false));
  Buffer.contents buffer

let quote s =
  let b=Buffer.create (String.length s+2) in Buffer.add_char b '"';
  String.iter (function
    | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n" | '\r' -> Buffer.add_string b "\\r" | '\t' -> Buffer.add_string b "\\t"
    | c when Char.code c<32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';Buffer.contents b
let obj fields = "{" ^ String.concat "," (List.map (fun (k,v) -> quote k ^ ":" ^ v) fields) ^ "}"
let array f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"

let rec value = function
  | S.Number n -> obj ["kind",quote "number";"exact",quote (S.Rational.to_string n)]
  | Boolean b -> obj ["kind",quote "boolean";"value",string_of_bool b]
  | Parameter name -> obj ["kind",quote "parameter";"name",quote name]
  | Sample id -> obj ["kind",quote "sample";"id",string_of_int id]
  | Unit -> obj ["kind",quote "unit"] | Nil -> obj ["kind",quote "nil"]
  | Arith (op,a,b) -> binary "arithmetic" (S.arith_name op) a b
  | Compare (op,a,b) -> binary "comparison" (S.compare_name op) a b
  | And (a,b) -> binary "boolean" "and" a b | Or (a,b) -> binary "boolean" "or" a b
  | Not t -> obj ["kind",quote "not";"operand",value t]
  | Ite (c,a,b) -> obj ["kind",quote "ite";"condition",value c;"then",value a;"else",value b]
  | Pair (a,b) -> obj ["kind",quote "pair";"first",value a;"second",value b]
  | Cons (a,b) -> obj ["kind",quote "cons";"head",value a;"tail",value b]
  | Closure c -> obj ["kind",quote "closure";"parameter",quote c.param;
      "self",(match c.self with None -> "null" | Some name -> quote name);
      "body",quote (Ast.to_string c.body);
      "environment",array (fun (name,v) -> obj ["name",quote name;"value",value v]) c.env]
and binary kind op a b = obj ["kind",quote kind;"op",quote op;"left",value a;"right",value b]

let boundary b =
  obj (["path",value b.boundary.path;"guard",value b.boundary.guard;
    "local_minus",value b.boundary.minus;"local_plus",value b.boundary.plus;
    "minus",(match b.minus with None -> "null" | Some v -> value v);
    "plus",(match b.plus with None -> "null" | Some v -> value v);
    "solver",quote (Solver.status b.answer);"retained",string_of_bool (retained_answer b.answer);
    "exceptional_conditions",array value b.exceptional_conditions;
    "trace_region",(match b.trace_region with None -> "null" | Some v -> value v);
    "integration_region",(match b.integration_region with None -> "null" | Some v -> value v)] @
    match b.answer with
    | Solver.Unknown reason | Solver.Redundant reason -> ["reason",quote reason]
    | _ -> [])

let json report = obj ["schema_version","5";
  "trace_semantics",quote "one_sided_limits";
  "refinement_scope",quote "sample_surface_almost_everywhere_at_fixed_parameters";
  "value",value report.analysis.value;
  "refined_value",value report.refined_value;
  "samples",array (fun (s:S.sample) -> obj ["id",string_of_int s.id;
    "distribution",quote (Ast.distribution_name s.distribution)]) report.analysis.samples;
  "candidates",array boundary report.checked;
  "retained_count",string_of_int (List.length (retained report))]
