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
  prerr_endline "usage: diff_ppl [--print-all] [--ad | --ad-dual] [--at PARAM=VALUE] [PARAM=VALUE ...] [dPARAM=SEED ...] FILE.slice";
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

type assignment =
  { name : string
  ; value : float
  }

type ad_args =
  { values : assignment list
  ; seeds : Slice.Adev.seeds option
  ; cut_order_at : Slice.Cut_order.at option
  }

let parse_assignment spec =
  try
    let idx = String.index spec '=' in
    let name = String.sub spec 0 idx in
    let value_text = String.sub spec (idx + 1) (String.length spec - idx - 1) in
    if name = "" || value_text = "" then usage ();
    { name; value = float_of_string value_text }
  with
  | Not_found | Failure _ -> usage ()

let is_seed_name name =
  String.length name > 1 && String.get name 0 = 'd'

let seed_var_name name =
  String.sub name 1 (String.length name - 1)

let parse_ad_args assignments =
  let values, seed_values =
    List.fold_left
      (fun (values, seed_values) assignment ->
         if is_seed_name assignment.name then
           (values, assignment :: seed_values)
         else
           (assignment :: values, seed_values))
      ([], [])
      assignments
  in
  let values = List.rev values in
  let seed_values = List.rev seed_values in
  let seeds =
    match seed_values, values with
    | [], [] -> None
    | [], { name; _ } :: _ -> Some (Slice.Adev.seeds_of_param name)
    | _ ->
        Some
          (List.fold_left
             (fun acc { name; value } ->
                Slice.Adev.add_seed (seed_var_name name) value acc)
             Slice.Adev.no_seeds
             seed_values)
  in
  let cut_order_at =
    match values with
    | { name; value } :: _ -> Some { Slice.Cut_order.param = name; value }
    | [] -> None
  in
  { values; seeds; cut_order_at }

let apply_values_raw values e =
  List.fold_left
    (fun acc { name; value } -> Slice.Simplify.subst_float name value acc)
    e
    values

let apply_values_simplified values e =
  Slice.Simplify.algebraic (apply_values_raw values e)

let run ~print_all ~mode ~assignments filename =
  let ad_args = parse_ad_args assignments in
  let source = read_file filename in
  let expr = Slice.Parse.parse_expr source in
  let normalized = Slice.Normalize.normalize expr in
  let texpr = Slice.Inference.infer normalized in
  let cut_order_at = ad_args.cut_order_at in
  let seeds = ad_args.seeds in
  let transformed = Slice.Discretization.discretize_top ?cut_order_at texpr in
  let ad_output =
    match mode with
    | Discretize -> None
    | AdGradient ->
        let discretized_texpr = Slice.Inference.infer transformed in
        let raw = Slice.Adev.gradient_raw ?seeds discretized_texpr in
        let simplified = Slice.Adev.gradient ?seeds discretized_texpr in
        Some
          { raw = apply_values_raw ad_args.values raw
          ; simplified = apply_values_simplified ad_args.values simplified
          }
    | AdDual ->
        let discretized_texpr = Slice.Inference.infer transformed in
        let raw = Slice.Adev.dual_expectation_raw ?seeds discretized_texpr in
        let simplified = Slice.Adev.dual_expectation ?seeds discretized_texpr in
        Some
          { raw = apply_values_raw ad_args.values raw
          ; simplified = apply_values_simplified ad_args.values simplified
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
  let rec parse_args print_all mode assignments filename = function
    | [] ->
        (match filename with
         | Some f -> run ~print_all ~mode ~assignments:(List.rev assignments) f
         | None -> usage ())
    | "--print-all" :: rest ->
        parse_args true mode assignments filename rest
    | "--ad" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all AdGradient assignments filename rest
    | "--ad-dual" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all AdDual assignments filename rest
    | "--at" :: spec :: rest ->
        parse_args print_all mode (parse_assignment spec :: assignments) filename rest
    | arg :: rest when String.length arg > 5 && String.sub arg 0 5 = "--at=" ->
        let spec = String.sub arg 5 (String.length arg - 5) in
        parse_args print_all mode (parse_assignment spec :: assignments) filename rest
    | arg :: rest when String.contains arg '=' ->
        parse_args print_all mode (parse_assignment arg :: assignments) filename rest
    | arg :: rest ->
        if filename <> None then usage ();
        parse_args print_all mode assignments (Some arg) rest
  in
  match Array.to_list Sys.argv with
  | _ :: args -> parse_args false Discretize [] None args
  | [] -> usage ()
