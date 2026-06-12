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
  prerr_endline "usage: diff_ppl [--print-all] [--ad | --ad-dual] [--at PARAM=VALUE] FILE.slice";
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

type eval_point =
  { param : string
  ; value : float
  }

let parse_eval_point spec =
  try
    let idx = String.index spec '=' in
    let param = String.sub spec 0 idx in
    let value_text = String.sub spec (idx + 1) (String.length spec - idx - 1) in
    if param = "" || value_text = "" then usage ();
    { param; value = float_of_string value_text }
  with
  | Not_found | Failure _ -> usage ()

let apply_eval_point_raw at e =
  match at with
  | None -> e
  | Some { param; value } -> Slice.Simplify.subst_float param value e

let apply_eval_point_simplified at e =
  match at with
  | None -> e
  | Some { param; value } ->
      Slice.Simplify.expr (Slice.Simplify.subst_float param value e)

let run ~print_all ~mode ~at filename =
  let source = read_file filename in
  let expr = Slice.Parse.parse_expr source in
  let normalized = Slice.Normalize.normalise expr in
  let texpr = Slice.Inference.infer normalized in
  let transformed = Slice.Discretization.discretize_top texpr in
  let ad_param =
    match at with
    | Some { param; _ } -> param
    | None -> "theta"
  in
  let ad_output =
    match mode with
    | Discretize -> None
    | AdGradient ->
        let discretized_texpr = Slice.Inference.infer transformed in
        let raw = Slice.Adev.gradient_raw ~param:ad_param discretized_texpr in
        let simplified = Slice.Adev.gradient ~param:ad_param discretized_texpr in
        Some
          { raw = apply_eval_point_raw at raw
          ; simplified = apply_eval_point_simplified at simplified
          }
    | AdDual ->
        let discretized_texpr = Slice.Inference.infer transformed in
        let raw = Slice.Adev.dual_expectation_raw ~param:ad_param discretized_texpr in
        let simplified = Slice.Adev.dual_expectation ~param:ad_param discretized_texpr in
        Some
          { raw = apply_eval_point_raw at raw
          ; simplified = apply_eval_point_simplified at simplified
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
  let rec parse_args print_all mode at filename = function
    | [] ->
        if mode = Discretize && at <> None then usage ();
        (match filename with
         | Some f -> run ~print_all ~mode ~at f
         | None -> usage ())
    | "--print-all" :: rest ->
        parse_args true mode at filename rest
    | "--ad" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all AdGradient at filename rest
    | "--ad-dual" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all AdDual at filename rest
    | "--at" :: spec :: rest ->
        if at <> None then usage ();
        parse_args print_all mode (Some (parse_eval_point spec)) filename rest
    | arg :: rest when String.length arg > 5 && String.sub arg 0 5 = "--at=" ->
        if at <> None then usage ();
        let spec = String.sub arg 5 (String.length arg - 5) in
        parse_args print_all mode (Some (parse_eval_point spec)) filename rest
    | arg :: rest ->
        if filename <> None then usage ();
        parse_args print_all mode at (Some arg) rest
  in
  match Array.to_list Sys.argv with
  | _ :: args -> parse_args false Discretize None None args
  | [] -> usage ()
