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
  prerr_endline "usage: diff_ppl [--print-all] FILE.slice";
  exit 2

let print_section title body =
  Printf.printf "== %s ==\n%s\n\n" title body

let run ~print_all filename =
  let source = read_file filename in
  let expr = Slice.Parse.parse_expr source in
  let normalized = Slice.Normalize.normalise expr in
  let texpr = Slice.Inference.infer normalized in
  let transformed = Slice.Discretization.discretize_top texpr in
  let transformed_source = Slice.Pretty.string_of_expr transformed in
  if print_all then (
    print_section "Source program" source;
    print_section "Normalized program" (Slice.Pretty.string_of_expr normalized);
    print_section "Typed AST" (Slice.Pretty.string_of_texpr texpr);
    print_section "Output program" transformed_source)
  else
    print_endline transformed_source

let () =
  match Array.to_list Sys.argv with
  | [_; filename] -> run ~print_all:false filename
  | [_; "--print-all"; filename] -> run ~print_all:true filename
  | _ -> usage ()
