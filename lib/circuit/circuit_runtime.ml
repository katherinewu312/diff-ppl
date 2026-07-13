(** Direct numeric evaluation of a compiled arithmetic circuit.

    The CLI currently reifies the circuit and deliberately reuses the
    existing deterministic Slice evaluator/AD transformations.  This small
    runtime is useful for circuit-specific tests and for a future compile-once,
    evaluate-many API. *)

let fail message = failwith ("Circuit runtime: " ^ message)

let eval arithmetic root assignments =
  let environment = Hashtbl.create (max 16 (List.length assignments)) in
  List.iter (fun (name, value) -> Hashtbl.replace environment name value) assignments;
  let values = Array.make (Circuit_ir.node_count arithmetic) 0.0 in
  let value id = values.(id) in
  List.iter
    (fun id ->
       values.(id) <-
         match Circuit_ir.lookup arithmetic id with
         | Circuit_ir.Const constant -> constant
         | Circuit_ir.Param name ->
             (match Hashtbl.find_opt environment name with
              | Some value -> value
              | None -> fail ("missing value for parameter " ^ name))
         | Circuit_ir.Add (left, right) -> value left +. value right
         | Circuit_ir.Sub (left, right) -> value left -. value right
         | Circuit_ir.Mul (left, right) -> value left *. value right
         | Circuit_ir.Div (left, right) -> value left /. value right
         | Circuit_ir.Special (name, arguments) ->
             let arguments =
               Array.to_list (Array.map value arguments)
             in
             (match Simplify.special_value name arguments with
              | Some result -> result
              | None -> fail ("unsupported special function " ^ name)))
    (Circuit_ir.reachable arithmetic root);
  values.(root)

