open Path
module S = Symbolic

let terms ts = String.concat ", " (List.map S.to_string ts)
let sample s = Distribution.name s.distribution ^ "(" ^ terms s.parameters ^ ")"

(** A path's probability, evaluated numerically once it has no parameters. *)
type probability =
  | Exact of Integration.Expr.t * float option
  | Unsupported of string

let probability s =
  let open Integration in
  match Integrate.probability s with
  | exception Integrate.Unsupported msg -> Unsupported msg
  | e when Expr.parameters [] e <> [] -> Exact (e, None)
  | e ->
      (match Numeric.value e with
       | v -> Exact (e, Some v)
       | exception Gsl.Error.Gsl_exn (_,msg) -> Unsupported ("numerical integration failed: " ^ msg))

let show_probability = function
  | Exact (e, Some v) when Integration.Expr.has_integral e ->
      Integration.Expr.number v ^ " (numerical integration)"
  | Exact (_, Some v) -> Integration.Expr.number v
  | Exact (e, None) -> Integration.Expr.to_string e
  | Unsupported msg -> "unsupported (" ^ msg ^ ")"

let status = function
  | Returned _ -> "returned"
  | Stopped (_,Rejected) -> "rejected"
  | Stopped (_,Step_limit) -> "step_limit"
  | Stopped (_,Runtime_error _) -> "runtime_error"

let text (result : Execute.result) =
  let buffer = Buffer.create 1024 in
  let line fmt = Printf.bprintf buffer (fmt ^^ "\n") in
  line "Symbolic execution: %d paths (%s)" (List.length result.paths)
    (if result.complete then "complete exploration; feasibility not fully checked" else "INCOMPLETE");
  let probabilities = List.map (fun o -> probability (state o)) result.paths in
  List.iteri (fun i (outcome,p) ->
    let s = state outcome in
    line "\nPath %d [%s]" (i+1) (status outcome);
    List.iter (fun x -> line "  sample#%d ~ %s" x.id (sample x)) s.samples;
    line "  condition: %s" (if s.constraints=[] then "true" else
      String.concat " && " (List.map S.to_string s.constraints));
    List.iter (fun term -> line "  observe: %s" (S.to_string term)) s.observations;
    List.iter (fun term -> line "  requires: %s" (S.to_string term)) s.requirements;
    (match outcome with
     | Returned (_,v) -> line "  return: %s" (Value.to_string v)
     | Stopped (_,Runtime_error msg) -> line "  error: %s" msg
     | Stopped (_,Rejected) -> line "  observation failed"
     | Stopped (_,Step_limit) -> line "  step bound reached; path was not discarded");
    Store.iter (fun id v -> line "  ref#%d = %s" id (Value.to_string v)) s.store;
    line "  probability: %s" (show_probability p)
  ) (List.combine result.paths probabilities);
  let values = List.filter_map (function Exact (_,v) -> v | Unsupported _ -> None) probabilities in
  if List.length values = List.length probabilities then begin
    let sum ps = List.fold_left (fun acc (o,p) -> match p with
      | Exact (_,Some v) when status o <> "rejected" -> acc +. v | _ -> acc) 0. ps in
    let paired = List.combine result.paths probabilities in
    line "\nTotal probability: %s" (Integration.Expr.number (List.fold_left (+.) 0. values));
    if List.exists (fun o -> status o = "rejected") result.paths then
      line "Probability of not being rejected: %s" (Integration.Expr.number (sum paired))
  end;
  Buffer.contents buffer

(* JSON contains structured scalar terms and distributions, so future layers do not
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
  | Value.Scalar t -> term t
  | Value.Pair (a,b) -> object_ ["kind",quote "pair";"first",json_value a;"second",json_value b]
  | Value.Cons (a,b) -> object_ ["kind",quote "cons";"head",json_value a;"tail",json_value b]
  | Value.Nil -> object_ ["kind",quote "nil"]
  | Value.Unit -> object_ ["kind",quote "unit"]
  | Value.Location id -> object_ ["kind",quote "reference";"id",string_of_int id]
  | Value.Closure _ as v -> object_ ["kind",quote "closure";"display",quote (Value.to_string v)]

let json_sample s =
  object_ ["id",string_of_int s.id;"distribution",quote (Distribution.name s.distribution);
    "parameters",array term s.parameters]

let rec expr e =
  let open Integration.Expr in
  let node kind fields = object_ (("kind",quote kind) :: fields) in
  let op name a b = node name ["left",expr a;"right",expr b] in
  let fn name a = node name ["operand",expr a] in
  match e with
  | Const c -> node "number" ["value",number c]
  | Param p -> node "parameter" ["name",quote p]
  | Var k -> node "sample" ["id",string_of_int k]
  | Add (a,b) -> op "add" a b | Sub (a,b) -> op "sub" a b
  | Mul (a,b) -> op "mul" a b | Div (a,b) -> op "div" a b
  | Min (a,b) -> op "min" a b | Max (a,b) -> op "max" a b
  | Exp a -> fn "exp" a | Erf a -> fn "erf" a | Ceil a -> fn "ceil" a
  | Indicator c -> node "indicator" ["condition",condition c]
  | Cdf (d,ps,x) ->
      node "cdf" ["distribution",quote (Distribution.name d);"parameters",array expr ps;"at",expr x]
  | Integral i ->
      let bound = function None -> "null" | Some e -> expr e in
      node "integral" ["sample",string_of_int i.var;
        "distribution",quote (Distribution.name i.distribution);
        "parameters",array expr i.parameters;
        "lower",bound i.lower;"upper",bound i.upper;"body",expr i.body]
and condition c =
  let open Integration.Expr in
  match c with
  | Compare (op,a,b) ->
      object_ ["kind",quote (match op with Lt -> "lt" | Le -> "le" | Eq -> "eq");
        "left",expr a;"right",expr b]
  | Not c -> object_ ["kind",quote "not";"operand",condition c]
  | Bool_param p -> object_ ["kind",quote "parameter";"name",quote p]

let json_probability = function
  | Exact (e,v) ->
      object_ ["expression",expr e;"display",quote (Integration.Expr.to_string e);
        "value",(match v with Some v -> Integration.Expr.number v | None -> "null")]
  | Unsupported msg -> object_ ["error",quote msg]

let json_path o =
  let s = state o in
  object_ (["status",quote (status o);
    "constraints",array term s.constraints;"observations",array term s.observations;
    "requirements",array term s.requirements;"samples",array json_sample s.samples;
    "store",array (fun (id,v) -> object_ ["id",string_of_int id;"value",json_value v]) (Store.bindings s.store);
    "probability",json_probability (probability s)] @
    match o with
    | Returned (_,v) -> ["return",json_value v]
    | Stopped (_,Runtime_error msg) -> ["error",quote msg]
    | Stopped _ -> [])

let json (result : Execute.result) = object_ ["schema_version","1";"complete",string_of_bool result.complete;
  "feasibility_checked","false";"paths",array json_path result.paths]
