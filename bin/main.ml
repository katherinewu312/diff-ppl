let read_file filename =
  let ic = open_in filename in
  try
    let len = in_channel_length ic in
    let content = really_input_string ic len in
    close_in ic;
    content
  with exn ->
    close_in_noerr ic;
    raise exn

let usage () =
  prerr_endline "usage: diff_ppl [--print-all] [--ad | --ad-dual] FILE.slice";
  exit 2

let print_section title body =
  Printf.printf "== %s ==\n%s\n\n" title body

type mode =
  | Discretize
  | AdGradient
  | AdDual

type ad_output =
  { raw : Slice.Ast.expr
  ; simplified : Slice.Ast.expr
  }

let run ~print_all ~mode filename =
  let source = read_file filename in
  let expr = Slice.Parse.parse_expr source in
  let normalized = Slice.Normalize.normalise expr in
  let texpr = Slice.Inference.infer normalized in
  let transformed = Slice.Discretization.discretize_top texpr in
  let ad_output =
    match mode with
    | Discretize -> None
    | AdGradient ->
        let discretized_texpr = Slice.Inference.infer transformed in
        Some
          { raw = Slice.Adev.gradient_raw discretized_texpr
          ; simplified = Slice.Adev.gradient discretized_texpr
          }
    | AdDual ->
        let discretized_texpr = Slice.Inference.infer transformed in
        Some
          { raw = Slice.Adev.dual_expectation_raw discretized_texpr
          ; simplified = Slice.Adev.dual_expectation discretized_texpr
          }
  in
  let output_expr =
    match ad_output with
    | None -> transformed
    | Some e -> e.simplified
  in
  let output_source = Slice.Pretty.string_of_expr output_expr in
  if print_all then (
    print_section "Source program" source;
    print_section "Normalized program" (Slice.Pretty.string_of_expr normalized);
    print_section "Typed AST" (Slice.Pretty.string_of_texpr texpr);
    print_section "Discretized program" (Slice.Pretty.string_of_expr transformed);
    (match ad_output with
     | None -> ()
     | Some { raw; simplified } ->
         let raw_title, simplified_title =
           match mode with
           | Discretize -> "Raw output program", "Output program"
           | AdGradient -> "Raw ADEV gradient program", "Simplified ADEV gradient program"
           | AdDual -> "Raw ADEV dual program", "Simplified ADEV dual program"
         in
         print_section raw_title (Slice.Pretty.string_of_expr raw);
         print_section simplified_title (Slice.Pretty.string_of_expr simplified)))
  else
    print_endline output_source

let () =
  let rec parse_args print_all mode filename = function
    | [] ->
        (match filename with
         | Some f -> run ~print_all ~mode f
         | None -> usage ())
    | "--print-all" :: rest ->
        parse_args true mode filename rest
    | "--ad" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all AdGradient filename rest
    | "--ad-dual" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all AdDual filename rest
    | arg :: rest ->
        if filename <> None then usage ();
        parse_args print_all mode (Some arg) rest
  in
  match Array.to_list Sys.argv with
  | _ :: args -> parse_args false Discretize None args
  | [] -> usage ()
