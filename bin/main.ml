let read_file filename =
  let channel = open_in_bin filename in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let () =
  let config = ref Slice.Execute.default_config in
  let json = ref false and filename = ref None and parameters = ref [] in
  let parameter assignment =
    match String.split_on_char '=' assignment with
    | [name;value] when name<>"" ->
        (try parameters := (name,float_of_string value)::!parameters
         with Failure _ -> raise (Arg.Bad "Expected NAME=NUMBER"))
    | _ -> raise (Arg.Bad "Expected NAME=NUMBER")
  in
  let options = [
    "--max-recursion",Arg.Int (fun n -> config := {!config with max_recursion=n}),
      "N Maximum nested fix applications per path (default 32)";
    "--max-steps",Arg.Int (fun n -> config := {!config with max_steps=n}),
      "N Maximum expression evaluations per path (default 10000)";
    "--max-paths",Arg.Int (fun n -> config := {!config with max_paths=n}),
      "N Exploration leaf budget; exceeding it fails (default 10000)";
    "--json",Arg.Set json," Emit structured JSON";
    "--at",Arg.String parameter," NAME=NUMBER Substitute a concrete parameter";
  ] in
  let usage = "Usage: diff_ppl [OPTIONS] FILE.slice\nLayer 1 symbolic execution (no probability integration or AD yet)." in
  Arg.parse options (fun path -> match !filename with
    | None -> filename := Some path
    | Some _ -> raise (Arg.Bad "Expected exactly one input file")) usage;
  try
    let filename = match !filename with
      | Some f -> f | None -> Arg.usage options usage; exit 2 in
    let expr = Slice.Parse.parse_expr (read_file filename) in
    let result = Slice.Execute.run ~config:!config ~parameters:!parameters expr in
    print_endline (if !json then Slice.Report.json result else Slice.Report.text result);
    if not result.complete then exit 2
  with
  | Slice.Execute.Path_limit n ->
      Printf.eprintf "Exploration exceeded --max-paths %d; no partial result emitted.\n" n; exit 2
  | Failure msg | Invalid_argument msg | Sys_error msg -> prerr_endline msg; exit 2
  | Stack_overflow -> prerr_endline "Host stack exhausted; lower execution bounds."; exit 2
