let read_file filename =
  let channel=open_in_bin filename in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let () =
  let filename=ref None and json=ref false and assignments=ref [] and timeout=ref 1000 in
  let assignment text = match String.split_on_char '=' text with
    | [name;n] when name<>"" -> assignments := (name,n)::!assignments
    | _ -> raise (Arg.Bad "Expected NAME=NUMBER") in
  let options=[
    "--json",Arg.Set json," Print the symbolic value and boundary records as JSON";
    "--at",Arg.String assignment," NAME=NUMBER Supply a concrete input instead of a symbolic parameter";
    "--solver-timeout-ms",Arg.Set_int timeout," N Z3 timeout per query (default 1000)";
  ] in
  let usage="Usage: diff_ppl [OPTIONS] FILE.ppl\nAnalyze the rules in tex/main.tex; Z3 checks reachability and boundary candidates." in
  Arg.parse options (fun name -> match !filename with
    | None -> filename:=Some name | Some _ -> raise (Arg.Bad "Expected one program file")) usage;
  try
    let filename=match !filename with Some f -> f | None -> Arg.usage options usage;exit 2 in
    let expression=Slice.Parse.parse_expr (read_file filename) in
    let inputs=Slice.Ast.free_variables expression |> Slice.Ast.Names.elements
      |> List.map (fun name -> name,Slice.Symbolic.Parameter name) in
    let parameters=List.map (fun (name,n) -> name,Slice.Symbolic.number n) !assignments @ inputs in
    let solver=Slice.Solver.create ~timeout_ms:!timeout () in
    let analysis=Slice.Execute.run ~solver ~parameters expression in
    let report=Slice.Report.check solver analysis in
    print_endline (if !json then Slice.Report.json report else Slice.Report.text report)
  with
  | Slice.Execute.Error message | Failure message | Invalid_argument message | Sys_error message ->
      prerr_endline message;exit 2
  | Slice.Symbolic.Rational.Overflow -> prerr_endline "Exact numeric literal exceeds the native rational range.";exit 2
  | Division_by_zero -> prerr_endline "Division by zero: the paper's arithmetic assumes defined expressions.";exit 2
  | Stack_overflow -> prerr_endline "No finite symbolic derivation completed; check the paper's termination assumptions.";exit 2
