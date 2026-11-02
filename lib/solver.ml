(** Only logical checks for the paper's reachability and boundary queries.
    This module does not integrate, differentiate, or change analysis rules. *)
module S = Symbolic

type answer = Sat | Unsat | Unknown of string
type t = { timeout_ms : int; cache : (string,answer) Hashtbl.t }
exception Unsupported of string
let create ?(timeout_ms=1000) () =
  if timeout_ms<1 then invalid_arg "Solver timeout must be positive";
  {timeout_ms;cache=Hashtbl.create 127}
let status = function Sat -> "sat" | Unsat -> "unsat" | Unknown _ -> "unknown"

let domains samples = List.fold_left (fun acc (s:S.sample) -> match s.distribution with
  | Ast.Uniform -> S.and_ acc (S.and_ (S.comparison Ast.Lt S.zero (S.Sample s.id))
      (S.comparison Ast.Lt (S.Sample s.id) S.one))
  | Gaussian -> acc) S.truth samples

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
    let num=if n.num<0 then Printf.sprintf "(- %d)" (-n.num) else string_of_int n.num in
    if n.den=1 then num else Printf.sprintf "(/ %s %d)" num n.den
  in
  let app op args = "(" ^ op ^ " " ^ String.concat " " args ^ ")" in
  let rec real = function
    | S.Number n -> numeral n
    | Parameter name -> variable ("parameter:" ^ name) "Real"
    | Sample id -> variable ("sample:" ^ string_of_int id) "Real"
    | Arith (Ast.Div,a,(Number n as b)) when n.num<>0 -> app "/" [real a;real b]
    | Arith (Ast.Div,_,_) ->
        raise (Unsupported "Symbolic division requires definedness assumptions not specified in the paper")
    | Arith (op,a,b) -> app (S.arith_name op) [real a;real b]
    | Ite (c,a,b) -> app "ite" [boolean c;real a;real b]
    | _ -> raise (Unsupported "SMT query requires a numeric value (functions are not compared extensionally)")
  and boolean = function
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
  String.concat "\n" (declarations @ ["(assert " ^ assertion ^ ")";"(check-sat)";"(exit)"])

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

(** Structural data equality; comparing different function values is deliberately
    UNKNOWN, because the paper supplies no extensional equality for closures. *)
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
  | _ when boolean_value a && boolean_value b ->
      S.or_ (S.and_ a (S.negate b)) (S.and_ (S.negate a) b)
  | _ -> S.negate (S.comparison Ast.Eq a b)

type boundary_check = { minus : S.t option; plus : S.t option; answer : answer }

(** Specialize the *final* value under a side assumption. Entailment, not
    spelling, determines comparison outcomes, including reversed/scaled guards.
    Conditions left unresolved are tracked: evaluating them at a shared zero
    without accounting for their side limits could give a false UNSAT result. *)
let specialize solver samples assumptions value =
  let unresolved=ref [] in
  let prove context c = match c with
    | S.Boolean b -> b | _ -> entails solver samples context c in
  let rec walk context = function
    | S.Compare (op,a,b) ->
        let a=walk context a and b=walk context b in
        let c=S.comparison op a b in
        if prove context c then S.truth
        else if prove context (S.negate c) then S.falsity
        else (
          unresolved := S.union !unresolved [S.arith Ast.Sub a b]; c)
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

let rec polynomial = function
  | S.Number _ | Parameter _ | Sample _ -> true
  | Arith (Ast.Div,a,Number n) -> n.num<>0 && polynomial a
  | Arith ((Ast.Add | Sub | Mul),a,b) -> polynomial a && polynomial b
  | _ -> false

let boundary solver samples ~value (b:S.boundary) =
  let none answer={minus=None;plus=None;answer} in
  let surface=S.and_ b.path (S.comparison Ast.Eq b.guard S.zero) in
  match query solver samples surface with
  | Unsat -> none Unsat
  | _ when not (polynomial b.guard) ->
      none (Unknown "Candidate guard is not a continuous polynomial; one-sided specialization is not certified")
  | _ ->
    let negative=S.and_ b.path (S.comparison Ast.Lt b.guard S.zero) in
    let positive=S.and_ b.path (S.comparison Ast.Lt S.zero b.guard) in
    if query solver samples negative=Unsat || query solver samples positive=Unsat then
      none (Unknown "A candidate side is infeasible; two-sided traces are not established")
    else
      try
        let minus,hm=specialize solver samples negative value in
        let plus,hp=specialize solver samples positive value in
        let with_sides answer={minus=Some minus;plus=Some plus;answer} in
        let unresolved=S.union hm hp in
        let at_intersection h = query solver samples
          (S.and_ surface (S.comparison Ast.Eq h S.zero))<>Unsat in
        let ambiguous=List.filter at_intersection unresolved in
        let regular_surface=List.fold_left (fun path h ->
          S.and_ path (S.negate (S.comparison Ast.Eq h S.zero))) surface ambiguous in
        let answer=query solver samples (S.and_ regular_surface (different minus plus)) in
        with_sides (match answer with
          | Unsat when ambiguous<>[] -> Unknown "Unresolved guards meet this surface; their one-sided traces are not established"
          | answer -> answer)
      with Unsupported reason -> none (Unknown reason)
