open Execute
module S = Symbolic

let rec value = function
  | Scalar t -> S.to_string t
  | Pair_value (a,b) -> "(" ^ value a ^ ", " ^ value b ^ ")"
  | Nil_value -> "nil"
  | Cons_value (a,b) -> "(" ^ value a ^ " :: " ^ value b ^ ")"
  | Unit_value -> "()"
  | Location id -> Printf.sprintf "ref#%d" id
  | Closure (arg,_,_) -> "<closure " ^ arg ^ ">"
  | Recursive (name,arg,_,_) -> "<recursive closure " ^ name ^ " " ^ arg ^ ">"

let kernel = function
  | Distribution (name,args) -> name ^ "(" ^ String.concat ", " (List.map S.to_string args) ^ ")"
  | Categorical args -> "discrete(" ^ String.concat ", " (List.map S.to_string args) ^ ")"
  | Bernoulli p -> "flip(" ^ S.to_string p ^ ")"

let status = function
  | Returned _ -> "returned"
  | Stopped (_,Rejected) -> "rejected"
  | Stopped (_,Recursion_limit) -> "recursion_limit"
  | Stopped (_,Step_limit) -> "step_limit"
  | Stopped (_,Runtime_error _) -> "runtime_error"

let state = function Returned (s,_) | Stopped (s,_) -> s

let text result =
  let buffer = Buffer.create 1024 in
  let line fmt = Printf.bprintf buffer (fmt ^^ "\n") in
  line "Symbolic execution: %d paths (%s)" (List.length result.paths)
    (if result.complete then "complete exploration; feasibility not fully checked" else "INCOMPLETE");
  List.iteri (fun i outcome ->
    let s = state outcome in
    line "\nPath %d [%s]" (i+1) (status outcome);
    List.iter (fun sample -> line "  sample#%d ~ %s" sample.id (kernel sample.kernel)) s.samplings;
    line "  condition: %s" (if s.constraints=[] then "true" else
      String.concat " && " (List.map S.to_string s.constraints));
    List.iter (fun term -> line "  observe: %s" (S.to_string term)) s.observations;
    List.iter (fun term -> line "  requires: %s" (S.to_string term)) s.requirements;
    (match outcome with
     | Returned (_,v) -> line "  return: %s" (value v)
     | Stopped (_,Runtime_error msg) -> line "  error: %s" msg
     | Stopped (_,Rejected) -> line "  observation failed"
     | Stopped (_,Recursion_limit) -> line "  recursion bound reached; path was not discarded"
     | Stopped (_,Step_limit) -> line "  step bound reached; path was not discarded");
    Store.iter (fun id v -> line "  ref#%d = %s" id (value v)) s.store
  ) result.paths;
  Buffer.contents buffer

(* JSON contains structured scalar terms and kernels, so future layers do not
   have to parse pretty-printed constraints. Closures/stores remain diagnostic. *)
let quote text =
  let b = Buffer.create (String.length text+2) in
  Buffer.add_char b '"';
  String.iter (function
    | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n" | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) text;
  Buffer.add_char b '"'; Buffer.contents b
let array f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"
let object_ fields = "{" ^ String.concat "," (List.map (fun (k,v) -> quote k ^ ":" ^ v) fields) ^ "}"
let rec term = function
  | S.Number n -> object_ ["kind",quote "number";"value",Printf.sprintf "%.17g" n]
  | S.Boolean b -> object_ ["kind",quote "boolean";"value",string_of_bool b]
  | S.Parameter name -> object_ ["kind",quote "parameter";"name",quote name]
  | S.Sample id -> object_ ["kind",quote "sample";"id",string_of_int id]
  | S.Finite (k,n) -> object_ ["kind",quote "finite";"value",string_of_int k;"size",string_of_int n]
  | S.Not t -> object_ ["kind",quote "not";"operand",term t]
  | S.Is_integer t -> object_ ["kind",quote "is_integer";"operand",term t]
  | S.Binary (op,a,b) -> object_ ["kind",quote "binary";"op",quote (S.op_string op);"left",term a;"right",term b]

let rec json_value = function
  | Scalar t -> term t
  | Pair_value (a,b) -> object_ ["kind",quote "pair";"first",json_value a;"second",json_value b]
  | Cons_value (a,b) -> object_ ["kind",quote "cons";"head",json_value a;"tail",json_value b]
  | Nil_value -> object_ ["kind",quote "nil"]
  | Unit_value -> object_ ["kind",quote "unit"]
  | Location id -> object_ ["kind",quote "reference";"id",string_of_int id]
  | (Closure _ | Recursive _) as v -> object_ ["kind",quote "closure";"display",quote (value v)]

let json_sampling s =
  let name,args = match s.kernel with
    | Distribution (name,args) -> name,args
    | Categorical args -> "discrete",args
    | Bernoulli p -> "flip",[p]
  in object_ ["id",string_of_int s.id;"distribution",quote name;"parameters",array term args]

let json_path o =
  let s = state o in
  object_ (["status",quote (status o);
    "constraints",array term s.constraints;"observations",array term s.observations;
    "requirements",array term s.requirements;"samples",array json_sampling s.samplings;
    "store",array (fun (id,v) -> object_ ["id",string_of_int id;"value",json_value v]) (Store.bindings s.store)] @
    match o with
    | Returned (_,v) -> ["return",json_value v]
    | Stopped (_,Runtime_error msg) -> ["error",quote msg]
    | Stopped _ -> [])

let json result = object_ ["schema_version","1";"complete",string_of_bool result.complete;
  "feasibility_checked","false";"paths",array json_path result.paths]
