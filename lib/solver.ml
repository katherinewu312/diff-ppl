(** Only logical checks for the paper's reachability and boundary queries.
    This module does not integrate, differentiate, or change analysis rules. *)
module S = Symbolic

type answer = Sat | Unsat | Redundant of string | Unknown of string
type t = { timeout_ms : int; cache : (string,answer) Hashtbl.t }
exception Unsupported of string
let create ?(timeout_ms=1000) () =
  if timeout_ms<1 then invalid_arg "Solver timeout must be positive";
  {timeout_ms;cache=Hashtbl.create 127}
let status = function
  | Sat -> "sat" | Unsat -> "unsat"
  | Redundant _ -> "redundant" | Unknown _ -> "unknown"

let domains samples = List.fold_left (fun acc (s:S.sample) -> match s.distribution with
  | Ast.Uniform -> S.and_ acc (S.and_ (S.comparison Ast.Lt S.zero (S.Sample s.id))
      (S.comparison Ast.Lt (S.Sample s.id) S.one))
  | Gaussian -> acc) S.truth samples

(* Identity comparison preserves existing sharing without traversing entire terms.
   Hashing is explicitly bounded, including for deeply shared expressions. *)
module Terms = Hashtbl.Make (struct
  type t = S.t
  let equal a b = a == b
  let hash value = Hashtbl.hash_param 10 10 value
end)

let smt query =
  let variables=Hashtbl.create 16 in
  let variable key sort =
    match Hashtbl.find_opt variables key with
    | Some (symbol,old_sort) when sort=old_sort -> symbol
    | Some _ -> raise (Unsupported "A symbolic variable is used with incompatible sorts")
    | None ->
        let symbol="v" ^ string_of_int (Hashtbl.length variables) in
        Hashtbl.add variables key (symbol,sort); symbol
  in
  let numeral (n:S.Rational.t) =
    (* Explicit Real numerals also type integer-only ite bodies correctly
       inside a Real definition; decimal .0 remains exact in SMT-LIB. *)
    let num=if n.num<0 then Printf.sprintf "(- %d.0)" (-n.num)
      else string_of_int n.num ^ ".0" in
    if n.den=1 then num else Printf.sprintf "(/ %s %d)" num n.den
  in
  let app op args = "(" ^ op ^ " " ^ String.concat " " args ^ ")" in
  let reals=Terms.create 64 and booleans=Terms.create 64 in
  let definitions=ref [] and next_definition=ref 0 in
  let define table sort value encode =
    match Terms.find_opt table value with
    | Some name -> name
    | None ->
        (* Encode dependencies first, then emit their user. Separate tables keep
           numeric and Boolean ite expressions in their respective sorts. *)
        let body=encode value in
        let name="t" ^ string_of_int !next_definition in
        incr next_definition;
        Terms.add table value name;
        definitions := Printf.sprintf "(define-fun %s () %s %s)" name sort body :: !definitions;
        name
  in
  let rec real value = match value with
    | S.Number _ | Parameter _ | Sample _ -> real_body value
    | _ -> define reals "Real" value real_body
  and real_body = function
    | S.Number n -> numeral n
    | Parameter name -> variable ("parameter:" ^ name) "Real"
    | Sample id -> variable ("sample:" ^ string_of_int id) "Real"
    | Arith (Ast.Div,a,(Number n as b)) when n.num<>0 -> app "/" [real a;real b]
    | Arith (Ast.Div,_,_) ->
        raise (Unsupported "Symbolic division requires definedness assumptions not specified in the paper")
    | Arith (op,a,b) -> app (S.arith_name op) [real a;real b]
    | Ite (c,a,b) -> app "ite" [boolean c;real a;real b]
    | _ -> raise (Unsupported "SMT query requires a numeric value (functions are not compared extensionally)")
  and boolean value = match value with
    | S.Boolean _ | Parameter _ -> boolean_body value
    | _ -> define booleans "Bool" value boolean_body
  and boolean_body = function
    | S.Boolean b -> string_of_bool b
    | Parameter name -> variable ("parameter:" ^ name) "Bool"
    | Compare (op,a,b) -> app (S.compare_name op) [real a;real b]
    | And (a,b) -> app "and" [boolean a;boolean b]
    | Or (a,b) -> app "or" [boolean a;boolean b]
    | Not a -> app "not" [boolean a]
    | Ite (c,a,b) -> app "ite" [boolean c;boolean a;boolean b]
    | _ -> raise (Unsupported "SMT query requires a Boolean condition")
  in
  let assertion=boolean query in
  let declarations=Hashtbl.to_seq_values variables |> List.of_seq
    |> List.sort compare |> List.map (fun (name,sort) -> "(declare-const " ^ name ^ " " ^ sort ^ ")") in
  String.concat "\n" (declarations @ List.rev !definitions @ ["(assert " ^ assertion ^ ")";"(check-sat)";"(exit)"])

let query solver samples condition =
  let formula=S.and_ (domains samples) condition in
  try
    let script=Printf.sprintf "(set-option :timeout %d)\n(set-logic ALL)\n%s\n"
      solver.timeout_ms (smt formula) in
    match Hashtbl.find_opt solver.cache script with
    | Some answer -> answer
    | None ->
        let answer =
          try
            let output,input,errors=Unix.open_process_args_full "z3"
              [|"z3";"-in";"-smt2"|] (Unix.environment ()) in
            let read channel =
              let b=Buffer.create 128 in
              (try while true do Buffer.add_string b (input_line channel);Buffer.add_char b '\n' done
               with End_of_file -> ()); Buffer.contents b in
            output_string input script; flush input;
            let stdout=read output and stderr=read errors in
            let code=Unix.close_process_full (output,input,errors) in
            let lines=String.split_on_char '\n' stdout |> List.map String.trim in
            if code<>Unix.WEXITED 0 || List.exists (fun s -> String.starts_with ~prefix:"(error" s) lines
            then Unknown ("Z3 error: " ^ String.trim (stdout ^ stderr))
            else if List.mem "unsat" lines then Unsat
            else if List.mem "sat" lines then Sat
            else Unknown "Z3 returned unknown (possibly timeout)"
          with Unix.Unix_error (e,_,_) -> Unknown ("Cannot run z3: " ^ Unix.error_message e)
        in Hashtbl.add solver.cache script answer;answer
  with Unsupported reason -> Unknown reason

let entails solver samples path condition =
  query solver samples (S.and_ path (S.negate condition))=Unsat

(** A small global pass.  Only solver-PROVED Boolean equivalences are merged;
    UNKNOWN never justifies a rewrite.  This is not geometric deduplication. *)
type normalization = {
  normalized_value : S.t;
  canonical : (S.t * S.t) list;
  original_atoms : S.t list;
}

let xor a b = S.or_ (S.and_ a (S.negate b)) (S.and_ (S.negate a) b)

let normalize_final solver samples value =
  let atoms=S.atomic_comparisons value in
  let representatives=ref [] and canonical=ref [] in
  List.iter (fun atom ->
    let representative=match List.find_opt (fun p ->
      query solver samples (xor atom p)=Unsat) !representatives with
      | Some p -> p
      | None -> representatives := !representatives @ [atom];atom in
    canonical := (atom,representative) :: !canonical) atoms;
  let canonical=List.rev !canonical in
  let memo=Terms.create 64 in
  let rec rewrite v =
    match Terms.find_opt memo v with
    | Some result -> result
    | None ->
        let result=match v with
          | S.Compare (op,a,b) ->
              let r=match List.assoc_opt v canonical with
                | Some representative -> representative
                | None -> v in
              if r<>v then rewrite r
              else S.comparison op (rewrite a) (rewrite b)
          | Arith (op,a,b) -> S.arith op (rewrite a) (rewrite b)
          | And (a,b) -> S.and_ (rewrite a) (rewrite b)
          | Or (a,b) -> S.or_ (rewrite a) (rewrite b)
          | Not a -> S.negate (rewrite a)
          | Ite (c,a,b) -> S.Ite (rewrite c,rewrite a,rewrite b)
          | Pair (a,b) -> S.Pair (rewrite a,rewrite b)
          | Cons (a,b) -> S.Cons (rewrite a,rewrite b)
          | other -> other in
        Terms.add memo v result;result
  in
  {normalized_value=S.simplify (rewrite value);canonical;original_atoms=atoms}

let globally_eliminated (n:normalization) (b:S.boundary) =
  let remaining=S.atomic_comparisons n.normalized_value in
  let originals=List.filter (function
    | S.Compare (_,a,c) -> S.arith Ast.Sub a c=b.guard
    | _ -> false) n.original_atoms in
  (* No conditional is left in the final output at all. *)
  if remaining=[] then true
  else if originals=[] then false
  else List.for_all (fun atom ->
    let canonical=match List.assoc_opt atom n.canonical with
      | Some x -> x | None -> atom in
    not (List.mem canonical remaining)) originals

(** Affine decomposition in base samples, with symbolic parameter-dependent
    coefficients.  Failure is conservative: nothing is assumed about the guard. *)
type affine = { constant : S.t; coeffs : (int * S.t) list }
let constant c = {constant=c;coeffs=[]}
let coefficient form id = match List.assoc_opt id form.coeffs with
  | Some c -> c | None -> S.zero
let simp op a b = S.simplify (S.arith op a b)
let affine_add op a b =
  let ids=List.sort_uniq compare (List.map fst a.coeffs @ List.map fst b.coeffs) in
  let coeffs=List.filter_map (fun id ->
    let v=simp op (coefficient a id) (coefficient b id) in
    if v=S.zero then None else Some (id,v)) ids in
  {constant=simp op a.constant b.constant;coeffs}
let affine_scale factor a =
  {constant=simp Ast.Mul factor a.constant;
   coeffs=List.filter_map (fun (id,c) ->
     let c=simp Ast.Mul factor c in
     if c=S.zero then None else Some (id,c)) a.coeffs}
let rec affine = function
  | (S.Number _ | S.Parameter _) as x -> Some (constant x)
  | S.Sample id -> Some {constant=S.zero;coeffs=[id,S.one]}
  | S.Arith (Ast.Add,a,b) ->
      (match affine a,affine b with
       | Some a,Some b -> Some (affine_add Ast.Add a b) | _ -> None)
  | S.Arith (Ast.Sub,a,b) ->
      (match affine a,affine b with
       | Some a,Some b -> Some (affine_add Ast.Sub a b) | _ -> None)
  | S.Arith (Ast.Mul,a,b) ->
      (match affine a,affine b with
       | Some a,Some b when a.coeffs=[] -> Some (affine_scale a.constant b)
       | Some a,Some b when b.coeffs=[] -> Some (affine_scale b.constant a)
       | _ -> None)
  | S.Arith (Ast.Div,a,S.Number n) when n.num<>0 ->
      (try match affine a with
       | Some a -> Some (affine_scale (S.Number (S.Rational.div S.Rational.one n)) a)
       | None -> None
       with S.Rational.Overflow -> None)
  | _ -> None

let equal_zero e = S.comparison Ast.Eq e S.zero

(** A guaranteed-nonzero pivot on the entire parameter domain.  If no single
    pivot is provable, conservatively decline the affine surface certificate. *)
let pivot solver samples a =
  List.find_opt (fun (_,c) -> query solver samples (equal_zero c)=Unsat) a.coeffs

(** Replacing < by <= is sound for closure only when its real operands
    are continuous.  Otherwise drop the constraint conservatively. *)
let rec continuous_real = function
  | S.Number _ | S.Parameter _ | S.Sample _ -> true
  | S.Arith ((Ast.Add | Ast.Sub | Ast.Mul),a,b) ->
      continuous_real a && continuous_real b
  | S.Arith (Ast.Div,a,S.Number n) -> n.num<>0 && continuous_real a
  | _ -> false

(** An overapproximation of the closure of a path condition.  Unsupported
    Boolean shapes are replaced by true, never strengthening reachability. *)
let rec relaxed_path = function
  | S.Boolean _ as c -> c
  | S.Compare (Ast.Lt,a,b) when continuous_real a && continuous_real b ->
      S.comparison Ast.Le a b
  | S.Compare (Ast.Le,a,b) as c when continuous_real a && continuous_real b -> c
  | S.Compare (Ast.Eq,a,b) as c when continuous_real a && continuous_real b -> c
  | S.Compare _ -> S.truth
  | S.And (a,b) -> S.and_ (relaxed_path a) (relaxed_path b)
  | S.Or (a,b) -> S.or_ (relaxed_path a) (relaxed_path b)
  | S.Not a -> relaxed_not a
  | _ -> S.truth
and relaxed_not = function
  | S.Boolean b -> S.Boolean (not b)
  | S.Compare (Ast.Lt,a,b) when continuous_real a && continuous_real b ->
      S.negate (S.comparison Ast.Lt a b)
  | S.Compare (Ast.Le,a,b) when continuous_real a && continuous_real b ->
      S.negate (S.comparison Ast.Lt a b)
  | S.Compare _ -> S.truth
  | S.Not a -> relaxed_path a
  | S.And (a,b) -> S.or_ (relaxed_not a) (relaxed_not b)
  | S.Or (a,b) -> S.and_ (relaxed_not a) (relaxed_not b)
  | _ -> S.truth

(** Proves that, for every allowed parameter value, the intersection with h=0
    has measure zero on g=0.  It uses the affine restriction of h to g's
    hyperplane, multiplying by the pivot instead of introducing division. *)
let coincidence_condition ~g_affine ~g_pivot h =
  match affine h with
  | None -> None
  | Some hf ->
      let j,aj=g_pivot in
      let bj=coefficient hf j in
      let c0=simp Ast.Sub
        (simp Ast.Mul aj hf.constant)
        (simp Ast.Mul bj g_affine.constant) in
      let ids=List.sort_uniq compare
        (List.map fst g_affine.coeffs @ List.map fst hf.coeffs) in
      let conditions=equal_zero c0 ::
        List.filter_map (fun i ->
          if i=j then None else
          let ci=simp Ast.Sub
            (simp Ast.Mul aj (coefficient hf i))
            (simp Ast.Mul bj (coefficient g_affine i)) in
          Some (equal_zero ci)) ids in
      Some (List.fold_left S.and_ S.truth conditions)

let negligible_intersection solver samples ~surface ~g_affine ~g_pivot h =
  match coincidence_condition ~g_affine ~g_pivot h with
  | None -> false
  | Some condition ->
      (* UNSAT proves h cannot vanish identically on g's hyperplane at
         any admissible parameters where the surface is feasible. *)
      query solver samples (S.and_ surface condition)=Unsat

let globally_same_surface solver samples (a:S.boundary) (b:S.boundary) =
  a.path=b.path &&
  (match affine a.guard,affine b.guard with
   | Some aform,Some bform when
       pivot solver samples aform<>None && pivot solver samples bform<>None ->
       query solver samples (xor (equal_zero a.guard) (equal_zero b.guard))=Unsat
   | _ -> false)

(** Structural data equality; comparing different functions is UNKNOWN. *)
let rec boolean_value = function
  | S.Boolean _ | Compare _ | And _ | Or _ | Not _ -> true
  | Ite (_,a,b) -> boolean_value a && boolean_value b
  | _ -> false

let rec different a b =
  if a=b then S.falsity else match a,b with
  | S.Pair (a,b),S.Pair (c,d) | Cons (a,b),Cons (c,d) -> S.or_ (different a c) (different b d)
  | Nil,Cons _ | Cons _,Nil -> S.truth
  | Boolean x,Boolean y -> S.Boolean (x<>y)
  | Closure _,_ | _,Closure _ -> raise (Unsupported "The paper does not define inequality between closures")
  | _ when boolean_value a && boolean_value b -> xor a b
  | _ -> S.negate (S.comparison Ast.Eq a b)

type boundary_check = {
  minus : S.t option;
  plus : S.t option;
  answer : answer;
  exceptional_conditions : S.t list;
  (* Regions are interpreted with the admissible sample domain. Limits and
     negligible intersections concern sample space at each fixed parameter.
     Geometric ownership does not certify parameter differentiability or
     interchangeable boundary velocities at exceptional coincidences. *)
  trace_region : S.t option;
  integration_region : S.t option;
}

(** Existing path-sensitive guarded specialization, unchanged. *)
let specialize solver samples assumptions value =
  let unresolved=ref [] in
  let prove context c = match c with
    | S.Boolean b -> b | _ -> entails solver samples context c in
  let contexts=Terms.create 32 in
  let rec walk context value =
    let values=match Terms.find_opt contexts context with
      | Some values -> values
      | None -> let values=Terms.create 64 in Terms.add contexts context values;values in
    match Terms.find_opt values value with
    | Some result -> result
    | None ->
        let result=walk_body context value in
        Terms.add values value result;result
  and walk_body context = function
    | S.Compare (op,a,b) ->
        let a=walk context a and b=walk context b in
        let c=S.comparison op a b in
        if prove context c then S.truth
        else if prove context (S.negate c) then S.falsity
        else (unresolved := S.union !unresolved [S.arith Ast.Sub a b];c)
    | Arith (op,a,b) -> S.arith op (walk context a) (walk context b)
    | And (a,b) -> S.and_ (walk context a) (walk context b)
    | Or (a,b) -> S.or_ (walk context a) (walk context b)
    | Not t -> S.negate (walk context t)
    | Ite (c,a,b) ->
        let c=walk context c in
        if prove context c then walk context a
        else if prove context (S.negate c) then walk context b
        else S.Ite (c,walk (S.and_ context c) a,walk (S.and_ context (S.negate c)) b)
    | Pair (a,b) -> S.Pair (walk context a,walk context b)
    | Cons (a,b) -> S.Cons (walk context a,walk context b)
    | t -> t
  in
  let value=walk assumptions value in value,!unresolved

let polynomial value =
  let cache=Terms.create 64 in
  let rec check value = match Terms.find_opt cache value with
    | Some result -> result
    | None ->
        let result=match value with
          | S.Number _ | Parameter _ | Sample _ -> true
          | Arith (Ast.Div,a,Number n) -> n.num<>0 && check a
          | Arith ((Ast.Add | Sub | Mul),a,b) -> check a && check b
          | _ -> false in
        Terms.add cache value result;result
  in check value

(** Flatten only addition/subtraction.  Matching terms can be canceled without
    making any assumptions about the choices of shared conditional guards. *)
let rec additive_terms sign = function
  | S.Arith (Ast.Add,a,b) -> additive_terms sign a @ additive_terms sign b
  | S.Arith (Ast.Sub,a,b) -> additive_terms sign a @ additive_terms (-sign) b
  | x -> [sign,x]

let independent_residual minus plus =
  let left=additive_terms 1 minus and right=additive_terms 1 plus in
  let terms=left @ List.map (fun (sign,t) -> -sign,t) right in
  let unique=List.sort_uniq compare (List.map snd terms) in
  let count t xs=List.fold_left (fun sum (sgn,x) -> if t=x then sum+sgn else sum) 0 xs in
  let canceled=List.filter (fun t ->
    List.exists (fun (_,x) -> x=t) left && List.exists (fun (_,x) -> x=t) right) unique in
  let residual=List.fold_left (fun sum t ->
    let n=count t terms in
    let rec append current n =
      if n=0 then current
      else if n>0 then append (S.arith Ast.Add current t) (n-1)
      else append (S.arith Ast.Sub current t) (n+1) in
    append sum n) S.zero unique |> S.simplify in
  residual,canceled

(** Verify that every canceled conditional is separately represented in B,
    with an unconditional path and not the same globally coincident surface.
    Otherwise, sharing that predicate could conceal the candidate's own jump. *)
let safe_canceled_conditionals solver samples candidate candidates canceled =
  let comparisons=List.fold_left (fun result term ->
    S.union result (S.atomic_comparisons term)) [] canceled in
  List.for_all (function
    | S.Compare (_,a,b) ->
        let guard=S.arith Ast.Sub a b in
        List.exists (fun (other:S.boundary) ->
          other.path=S.truth && other.guard=guard &&
          not (globally_same_surface solver samples candidate other)) candidates
    | _ -> false) comparisons

(** A sufficient zero-INDEPENDENT-jump certificate, not a geometric proof
    that the candidate's entire surface is continuous.  The common additive
    summands remain covered by their own recorded boundaries. *)
let zero_independent_jump solver samples ~surface ~candidate ~candidates minus plus =
  let residual,canceled=independent_residual minus plus in
  polynomial residual &&
  List.for_all S.total canceled &&
  safe_canceled_conditionals solver samples candidate candidates canceled &&
  query solver samples (S.and_ surface (different residual S.zero))=Unsat

(** Exact eventual evaluation on the rays z +/- epsilon * a_j e_j.
    Here g(z)=0 and a_j is a uniformly nonzero sample coefficient of g, so
    g has derivative +/- a_j^2. Parameters remain fixed. For an affine h,
    h(z +/- epsilon*n)=h(z) +/- epsilon*b_j*a_j exactly: comparisons must
    use both terms, rather than compare only the limits of their operands.

    At each parameter assignment, h either vanishes identically on g's plane
    (the coincidence condition C), or its zero set there is negligible. The
    formula C OR h<>0 retains the former and excludes only the latter. No
    enumeration of parameter strata or boundary patches is required. *)
let directional_limits ~gform ~g_pivot ~scope ~covered minus plus =
  let nodes=ref 4096 and guards=ref 256 in
  let guard_cache=Terms.create 64 and regularity=ref S.truth in
  let register atom = match Terms.find_opt guard_cache atom with
    | Some result -> result
    | None ->
        decr guards;
        if !guards<0 then raise (Unsupported "Directional guard budget exhausted");
        let h=match atom with
          | S.Compare (_,a,b) -> simp Ast.Sub a b
          | _ -> raise (Unsupported "Directional evaluation requires an atomic comparison") in
        let hf=match affine h with
          | Some form -> form
          | None -> raise (Unsupported "Directional evaluation requires guards affine in samples") in
        let j,aj=g_pivot in
        let slope=simp Ast.Mul (coefficient hf j) aj in
        let coincident=match coincidence_condition ~g_affine:gform ~g_pivot h with
          | Some c -> c
          | None -> raise (Unsupported "Affine intersection certificate unavailable") in
        regularity:=S.and_ !regularity (S.or_ coincident (S.negate (equal_zero h)));
        Terms.add guard_cache atom (h,slope);h,slope in
  let spend () =
    decr nodes;
    if !nodes<0 then raise (Unsupported "Directional evaluation budget exhausted") in
  let ray sign value =
    let memo=Terms.create 128 in
    let rec walk value=match Terms.find_opt memo value with
      | Some result -> result
      | None ->
          spend ();
          let result=match value with
            | S.Number _ | Boolean _ | Parameter _ | Sample _ | Unit | Nil -> value
            | Compare(op,_,_) ->
                let h,slope=register value in
                let slope=if sign<0 then simp Ast.Sub S.zero slope else slope in
                let tie=S.and_ (equal_zero h) (S.comparison op slope S.zero) in
                (match op with
                 | Ast.Lt | Le -> S.or_ (S.comparison Ast.Lt h S.zero) tie
                 | Eq -> tie)
            | Arith(Ast.Div,a,(Number n as b)) when n.num<>0 ->
                S.arith Ast.Div (walk a) b
            | Arith(Ast.Div,_,_) ->
                raise (Unsupported "Directional limits require a nonzero constant denominator")
            | Arith(op,a,b) -> S.arith op (walk a) (walk b)
            | And(a,b) -> S.and_ (walk a) (walk b)
            | Or(a,b) -> S.or_ (walk a) (walk b)
            | Not a -> S.negate (walk a)
            | Ite(c,a,b) ->
                let c=walk c in
                (match c with
                 | S.Boolean true -> walk a
                 | Boolean false -> walk b
                 | _ -> S.Ite(c,walk a,walk b))
            | Pair(a,b) -> S.Pair(walk a,walk b)
            | Cons(a,b) -> S.Cons(walk a,walk b)
            | Closure _ -> raise (Unsupported "One-sided function values are not compared extensionally") in
          Terms.add memo value result;result in
    S.simplify (walk value) in
  let minus=ray (-1) minus and plus=ray 1 plus in
  (* Scope and ownership predicates must also be locally constant on the
     remaining plane. This prevents SAT witnesses confined to intersections. *)
  let seen=Terms.create 64 in
  let rec conditions value = if not (Terms.mem seen value) then begin
    spend ();Terms.add seen value ();
    match value with
    | S.Compare _ -> ignore (register value)
    | And(a,b) | Or(a,b) -> conditions a;conditions b
    | Not a -> conditions a
    | Ite(c,a,b) -> conditions c;conditions a;conditions b
    | Boolean _ | Parameter _ -> ()
    | _ -> raise (Unsupported "Unsupported directional surface predicate")
  end in
  conditions scope;conditions covered;
  minus,plus,S.and_ scope !regularity

let boundary solver samples ?(candidates=[]) ?(covered=S.falsity) ~value (b:S.boundary) =
  (* Keep the candidates argument for existing callers. Coverage now comes
     only from previously certified integration representatives in Report. *)
  let _=candidates in
  let none answer={minus=None;plus=None;answer;exceptional_conditions=[];
    trace_region=None;integration_region=None} in
  let scope=S.and_ (relaxed_path b.path) (equal_zero b.guard) in
  match query solver samples scope with
  | Unsat -> none Unsat
  | Unknown why | Redundant why -> none (Unknown ("Surface feasibility: " ^ why))
  | Sat ->
      try
        let gform=match affine b.guard with
          | Some form -> form
          | None -> raise (Unsupported "Affine sample guard required for directional surface refinement") in
        let g_pivot=match pivot solver samples gform with
          | Some pivot -> pivot
          | None -> raise (Unsupported "No uniformly nonzero sample coefficient; possibly degenerate boundary") in
        (* Preserve ordinary guarded specialization as the first step. Its
           assumptions concern the complete output, not the local Rec values. *)
        let minus,_=specialize solver samples (S.comparison Ast.Lt b.guard S.zero) value in
        let plus,_=specialize solver samples (S.comparison Ast.Lt S.zero b.guard) value in
        let minus,plus,regular=directional_limits ~gform ~g_pivot ~scope ~covered minus plus in
        let owned=S.and_ regular (S.negate covered) in
        let with_sides answer={minus=Some minus;plus=Some plus;answer;exceptional_conditions=[];
          trace_region=Some regular;integration_region=Some owned} in
        let jump=different minus plus in
        (* On each fixed-parameter fiber these expressions are continuous on
           the remaining surface cells. A SAT witness therefore has a relatively
           open neighborhood of nonzero jump, not merely an isolated crossing. *)
        match query solver samples (S.and_ owned jump) with
        | Unsat when covered<>S.falsity ->
            (match query solver samples (S.and_ regular jump) with
             | Unsat -> with_sides Unsat
             | _ -> with_sides (Redundant "Any jump is represented by earlier retained surfaces"))
        | answer -> with_sides answer
      with Unsupported reason -> none (Unknown reason)
         | S.Rational.Overflow -> none (Unknown "Exact arithmetic overflow in directional refinement")
