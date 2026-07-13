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
  prerr_endline "usage: diff_ppl [--print-all] [--compile] [--expect] [--forward | --reverse | --reverse-runtime] [--ad | --ad-dual] [--at PARAM=VALUE] [PARAM=VALUE ...] [dPARAM=SEED ...] FILE.slice";
  exit 2

let print_section title body =
  Printf.printf "== %s ==\n%s\n\n" title body

let string_of_circuit_stats (stats : Slice.Circuit.stats) =
  Printf.sprintf
    "allocated random variables: %d\nreachable random variables: %d\nadditive terms: %d\nallocated decision nodes: %d\nreachable decision nodes: %d\nallocated arithmetic nodes: %d\nreachable arithmetic nodes: %d"
    stats.random_variables
    stats.reachable_random_variables
    stats.additive_terms
    stats.decision_nodes
    stats.eliminated_decision_nodes
    stats.arithmetic_nodes
    stats.reachable_arithmetic_nodes

type mode =
  | Discretize
  | Evaluate
  | AdGradient
  | AdDual

type ad_mode =
  | Forward
  | Reverse
  | ReverseRuntime

type ad_output =
  { raw : Slice.Ast.expr
  ; simplified : Slice.Ast.expr
  ; vector_output : vector_output
  }
and vector_output =
  | NoVector
  | GradientVector of string list
  | DualGradientVector of string list

type assignment =
  { name : string
  ; value : float
  ; is_at : bool
  }

type ad_args =
  { values : assignment list
  ; seeds : Slice.Forward.seeds option
  ; explicit_seeds : bool
  ; cut_order_at : Slice.Cut_order.at option
  }

let parse_assignment ?(is_at = false) spec =
  try
    let idx = String.index spec '=' in
    let name = String.sub spec 0 idx in
    let value_text = String.sub spec (idx + 1) (String.length spec - idx - 1) in
    if name = "" || value_text = "" then usage ();
    { name; value = float_of_string value_text; is_at }
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
  let at_values = List.filter (fun assignment -> assignment.is_at) values in
  let explicit_seeds = seed_values <> [] in
  let seeds =
    match seed_values, at_values with
    | [], [] -> None
    | [], { name; _ } :: _ -> Some (Slice.Forward.seeds_of_param name)
    | _ ->
        Some
          (List.fold_left
             (fun acc { name; value; _ } ->
                Slice.Forward.add_seed (seed_var_name name) value acc)
             Slice.Forward.no_seeds
             seed_values)
  in
  let cut_order_at =
    match values with
    | { name; value; _ } :: _ -> Some { Slice.Cut_order.param = name; value }
    | [] -> None
  in
  { values; seeds; explicit_seeds; cut_order_at }

let apply_values_raw values e =
  List.fold_left
    (fun acc { name; value; _ } -> Slice.Simplify.subst_float name value acc)
    e
    values

let apply_values_simplified values e =
  Slice.Simplify.algebraic (apply_values_raw values e)

let finalize_simplified_ad ad_mode values e =
  let simplified = apply_values_simplified values e in
    match ad_mode with
    | Forward | Reverse ->
        Slice.Simplify.evaluate_symbolically_or_original simplified
    | ReverseRuntime -> simplified

let free_float_var_names te =
  Slice.Util.free_float_vars te
  |> Slice.Util.StringSet.elements

let preserve_missing_parameters parameters expression =
  let present = Slice.Simplify.free_vars expression in
  let used_names =
    List.fold_left
      (fun names parameter -> Slice.Simplify.StringSet.add parameter names)
      present parameters
    |> ref
  in
  let rec fresh_binding () =
    let candidate = Slice.Util.fresh_var "_circuit_input" in
    if Slice.Simplify.StringSet.mem candidate !used_names then
      fresh_binding ()
    else begin
      used_names := Slice.Simplify.StringSet.add candidate !used_names;
      candidate
    end
  in
  List.fold_right
    (fun parameter body ->
       if Slice.Simplify.StringSet.mem parameter present then
         body
       else
         let binding = fresh_binding () in
         Slice.Ast.ExprNode
           (Slice.Ast.Let
              ( binding
              , Slice.Ast.ExprNode (Slice.Ast.Var parameter)
              , body )))
    parameters
    expression

let format_ad_expr vector_output e =
  match vector_output, e with
  | NoVector, _ -> Slice.Pretty.string_of_expr e
  | GradientVector labels, _ -> Slice.Pretty.string_of_labeled_expr_list labels e
  | DualGradientVector labels, _ -> Slice.Pretty.string_of_dual_with_labeled_expr_list labels e

let infer_with_cuts expr =
  expr
  |> Slice.Inference.infer
  |> Slice.Cut_inference.analyze

let run ~print_all ~compile ~mode ~ad_mode ~assignments filename =
  let ad_args = parse_ad_args assignments in
  let source = read_file filename in
  let expr = Slice.Parse.parse_expr source in
  let normalized = Slice.Normalize.normalize expr in
  let texpr = infer_with_cuts normalized in
  let cut_order_at = ad_args.cut_order_at in
  let seeds = ad_args.seeds in
  let forward_seeds =
    if ad_args.explicit_seeds then seeds else None
  in
  let reverse_seeds =
    if ad_args.explicit_seeds then seeds else None
  in
  let transformed = Slice.Discretization.discretize_top ?cut_order_at texpr in
  let compiled_circuit, original_circuit_parameters =
    if compile then
      let discretized_texpr = infer_with_cuts transformed in
      ( Some (Slice.Circuit.compile discretized_texpr)
      , free_float_var_names discretized_texpr )
    else
      None, []
  in
  let backend_expr =
    match compiled_circuit with
    | Some circuit -> Slice.Circuit.to_expr circuit
    | None -> transformed
  in
  let ad_backend_expr =
    match compiled_circuit, ad_args.explicit_seeds with
    | Some _, false ->
        preserve_missing_parameters original_circuit_parameters backend_expr
    | Some _, true | None, _ -> backend_expr
  in
  let ad_output =
    match mode with
    | Discretize -> None
    | Evaluate ->
        let discretized_texpr = infer_with_cuts backend_expr in
        let values =
          List.map
            (fun { name; value; _ } -> (name, value))
            ad_args.values
        in
        Some
          { raw = apply_values_raw ad_args.values (Slice.Expect.raw discretized_texpr)
          ; simplified = Slice.Expect.eval ~values discretized_texpr
          ; vector_output = NoVector
          }
    | AdGradient ->
        let discretized_texpr = infer_with_cuts ad_backend_expr in
        let vector_output =
          match ad_mode, ad_args.explicit_seeds with
          | Forward, false | Reverse, false | ReverseRuntime, false ->
              GradientVector (free_float_var_names discretized_texpr)
          | Forward, true | Reverse, true | ReverseRuntime, true -> NoVector
        in
        let raw, simplified =
          match ad_mode with
          | Forward ->
              ( Slice.Forward.gradient_raw ?seeds:forward_seeds discretized_texpr
              , Slice.Forward.gradient ?seeds:forward_seeds discretized_texpr )
          | Reverse ->
              ( Slice.Reverse.gradient_raw ?seeds:reverse_seeds discretized_texpr
              , Slice.Reverse.gradient ?seeds:reverse_seeds discretized_texpr )
          | ReverseRuntime ->
              if ad_args.explicit_seeds then
                failwith "Reverse runtime AD currently supports only full-gradient mode";
              let values =
                List.map
                  (fun { name; value; _ } -> (name, value))
                  ad_args.values
              in
              let gradient =
                Slice.Reverse.runtime_gradient values discretized_texpr
              in
              let raw =
                Slice.Reverse.runtime_gradient_raw values discretized_texpr
              in
              (raw, gradient)
        in
        let raw = apply_values_raw ad_args.values raw in
        Some
          { raw
          ; simplified = finalize_simplified_ad ad_mode ad_args.values simplified
          ; vector_output
          }
    | AdDual ->
        let discretized_texpr = infer_with_cuts ad_backend_expr in
        let vector_output =
          match ad_mode, ad_args.explicit_seeds with
          | Forward, false | Reverse, false ->
              DualGradientVector (free_float_var_names discretized_texpr)
          | Forward, true | Reverse, true -> NoVector
          | ReverseRuntime, _ ->
              failwith "Reverse runtime AD currently supports --ad, not --ad-dual"
        in
        let raw, simplified =
          match ad_mode with
          | Forward ->
              ( Slice.Forward.dual_expectation_raw ?seeds:forward_seeds discretized_texpr
              , Slice.Forward.dual_expectation ?seeds:forward_seeds discretized_texpr )
          | Reverse ->
              ( Slice.Reverse.dual_expectation_raw ?seeds:reverse_seeds discretized_texpr
              , Slice.Reverse.dual_expectation ?seeds:reverse_seeds discretized_texpr )
          | ReverseRuntime ->
              failwith "Reverse runtime AD currently supports --ad, not --ad-dual"
        in
        let raw = apply_values_raw ad_args.values raw in
        Some
          { raw
          ; simplified = finalize_simplified_ad ad_mode ad_args.values simplified
          ; vector_output
          }
  in
  let output_source =
    match ad_output with
    | None -> Slice.Pretty.string_of_expr backend_expr
    | Some e -> format_ad_expr e.vector_output e.simplified
  in
  if print_all then (
    print_section "Source program" source;
    print_section "Normalized program" (Slice.Pretty.string_of_expr normalized);
    print_section "Typed AST" (Slice.Pretty.string_of_texpr texpr);
    print_section "Discretized program" (Slice.Pretty.string_of_expr transformed);
    (match compiled_circuit with
     | None -> ()
     | Some circuit ->
         print_section "Compiled arithmetic circuit"
           (Slice.Pretty.string_of_expr (Slice.Circuit.to_expr circuit));
         print_section "Compiled circuit stats"
           (string_of_circuit_stats circuit.stats));
    (match ad_output with
     | None -> ()
     | Some { raw; simplified; vector_output } ->
          let ad_name =
            match ad_mode with
            | Forward -> "forward"
            | Reverse -> "reverse"
            | ReverseRuntime -> "reverse runtime"
          in
          let raw_title, simplified_title =
            match mode with
            | Discretize -> "Raw output program", "Output program"
            | Evaluate -> "Raw evaluation program", "Evaluation result"
            | AdGradient -> "Raw " ^ ad_name ^ " AD gradient program", "Simplified " ^ ad_name ^ " AD gradient program"
            | AdDual -> "Raw " ^ ad_name ^ " AD dual program", "Simplified " ^ ad_name ^ " AD dual program"
          in
         print_section raw_title (format_ad_expr vector_output raw);
         print_section simplified_title (format_ad_expr vector_output simplified)))
  else
    print_endline output_source

let () =
  let rec parse_args print_all compile mode ad_mode assignments filename = function
    | [] ->
        (match filename with
         | Some f ->
             (try run ~print_all ~compile ~mode ~ad_mode ~assignments:(List.rev assignments) f with
              | Failure msg ->
                  prerr_endline msg;
                  exit 1)
         | None -> usage ())
    | "--print-all" :: rest ->
        parse_args true compile mode ad_mode assignments filename rest
    | "--compile" :: rest ->
        parse_args print_all true mode ad_mode assignments filename rest
    | "--expect" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all compile Evaluate ad_mode assignments filename rest
    | "--forward" :: rest ->
        parse_args print_all compile mode Forward assignments filename rest
    | "--reverse" :: rest ->
        parse_args print_all compile mode Reverse assignments filename rest
    | "--reverse-runtime" :: rest ->
        parse_args print_all compile mode ReverseRuntime assignments filename rest
    | "--ad" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all compile AdGradient ad_mode assignments filename rest
    | "--ad-dual" :: rest ->
        if mode <> Discretize then usage ();
        parse_args print_all compile AdDual ad_mode assignments filename rest
    | "--at" :: spec :: rest ->
        parse_args print_all compile mode ad_mode (parse_assignment ~is_at:true spec :: assignments) filename rest
    | arg :: rest when String.length arg > 5 && String.sub arg 0 5 = "--at=" ->
        let spec = String.sub arg 5 (String.length arg - 5) in
        parse_args print_all compile mode ad_mode (parse_assignment ~is_at:true spec :: assignments) filename rest
    | arg :: rest when String.contains arg '=' ->
        parse_args print_all compile mode ad_mode (parse_assignment arg :: assignments) filename rest
    | arg :: rest ->
        if filename <> None then usage ();
        parse_args print_all compile mode ad_mode assignments (Some arg) rest
  in
  match Array.to_list Sys.argv with
  | _ :: args -> parse_args false false Discretize Forward [] None args
  | [] -> usage ()
