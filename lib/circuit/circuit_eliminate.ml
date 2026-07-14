(** Eliminate any finite random variables that remain in the lowered result.

    Float lowering normally emits its expected-value summary as an arithmetic
    leaf.  Boolean results, and exact DDs demanded while constructing a float
    summary, use this same memoized elimination machinery. *)

type result =
  { root : Circuit_ir.ac_id
  ; eliminated_dd_nodes : int
  }

let fail message = failwith ("Circuit elimination: " ^ message)

let eliminate (program : Circuit_lower.program) =
  (* Lowering may already have eliminated a DD to obtain a demanded exact
     expectation.  Reuse that work when finishing the program. *)
  let memo = program.elimination_memo in
  let rec visit dd =
    match Hashtbl.find_opt memo dd with
    | Some result -> result
    | None ->
        let result =
          match Circuit_dd.lookup program.decisions dd with
          | Circuit_dd.Leaf arithmetic -> arithmetic
          | Circuit_dd.Choice (variable, children) ->
              let weights =
                match Hashtbl.find_opt program.choices variable with
                | Some choice -> choice.Circuit_lower.weights
                | None ->
                    fail
                      (Printf.sprintf
                         "random variable %d has no probability table" variable)
              in
              if Array.length weights <> Array.length children then
                fail
                  (Printf.sprintf
                     "random variable %d has %d branches but %d weights"
                     variable (Array.length children) (Array.length weights));
              Array.mapi
                (fun index child ->
                   Circuit_ir.mul program.arithmetic weights.(index)
                     (visit child))
                children
              |> Circuit_ir.sum program.arithmetic
        in
        Hashtbl.add memo dd result;
        result
  in
  let roots = List.map visit program.result_parts in
  { root = Circuit_ir.sum_list program.arithmetic roots
  ; eliminated_dd_nodes = Hashtbl.length memo
  }
