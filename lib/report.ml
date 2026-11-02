module S = Symbolic
type checked = { boundary : S.boundary; minus : S.t option; plus : S.t option; answer : Solver.answer }
type t = { analysis : Execute.result; checked : checked list }

let check solver analysis =
  let checked=List.map (fun boundary ->
    let result=Solver.boundary solver analysis.Execute.samples ~value:analysis.value boundary in
    {boundary;minus=result.minus;plus=result.plus;answer=result.answer}) analysis.candidates in
  {analysis;checked}

let retained report = List.filter (fun b -> b.answer<>Solver.Unsat) report.checked
let tuple (b:S.boundary) = Printf.sprintf "(%s; %s; %s; %s)"
  (S.to_string b.path) (S.to_string b.guard) (S.to_string b.minus) (S.to_string b.plus)

let text report =
  let buffer=Buffer.create 1024 in
  let line fmt=Printf.bprintf buffer (fmt ^^ "\n") in
  line "Symbolic value: %s" (S.to_string report.analysis.value);
  line "\nBase samples:";
  List.iter (fun (s:S.sample) -> line "  s%d ~ %s" s.id (match s.distribution with
    | Ast.Uniform -> "Uniform(0, 1), 0 < s < 1"
    | Gaussian -> "Gaussian(0, 1), s in R")) report.analysis.samples;
  line "\nCandidate boundaries B: %d" (List.length report.checked);
  line "  (path; guard; v_minus; v_plus), exactly as recorded by Rec";
  List.iteri (fun i b ->
    line "  %d. %s" (i+1) (tuple b.boundary);
    (match b.minus,b.plus with
     | Some minus,Some plus -> line "     final-output sides: %s ; %s" (S.to_string minus) (S.to_string plus)
     | _ -> line "     final-output sides: unresolved");
    line "     %s: %s" (Solver.status b.answer) (match b.answer with
      | Solver.Unsat -> "dropped" | Sat -> "retained"
      | Unknown reason -> "retained (" ^ reason ^ ")")) report.checked;
  let boundaries=retained report in
  line "\nRetained boundaries B*: %d" (List.length boundaries);
  if boundaries=[] then line "  (none)";
  List.iteri (fun i b ->
    line "  %d. %s = 0 [%s]" (i+1) (S.to_string b.boundary.guard) (Solver.status b.answer);
    line "     path: %s" (S.to_string b.boundary.path);
    (match b.minus,b.plus with
     | Some minus,Some plus ->
         line "     output on g < 0: %s" (S.to_string minus);
         line "     output on g > 0: %s" (S.to_string plus)
     | _ -> line "     final-output sides: unresolved");
    match b.answer with
    | Solver.Unknown reason -> line "     unconfirmed candidate: %s" reason
    | _ -> ()) boundaries;
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
    "solver",quote (Solver.status b.answer);"retained",string_of_bool (b.answer<>Solver.Unsat)] @
    match b.answer with Solver.Unknown reason -> ["reason",quote reason] | _ -> [])

let json report = obj ["schema_version","3";"value",value report.analysis.value;
  "samples",array (fun (s:S.sample) -> obj ["id",string_of_int s.id;
    "distribution",quote (Ast.distribution_name s.distribution)]) report.analysis.samples;
  "candidates",array boundary report.checked;
  "retained_count",string_of_int (List.length (retained report))]
