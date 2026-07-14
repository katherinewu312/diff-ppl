(** Public facade for finite probabilistic-program circuit compilation. *)

type stats =
  { random_variables : int
  ; reachable_random_variables : int
  ; additive_terms : int
  ; decision_nodes : int
  ; eliminated_decision_nodes : int
  ; arithmetic_nodes : int
  ; reachable_arithmetic_nodes : int
  }

type t =
  { expression : Ast.expr
  ; arithmetic : Circuit_ir.t
  ; root : Circuit_ir.ac_id
  ; stats : stats
  }

let compile typed_expression =
  let lowered = Circuit_lower.lower typed_expression in
  let eliminated = Circuit_eliminate.eliminate lowered in
  let expression = Circuit_ir.reify lowered.arithmetic eliminated.root in
  let module Int_set = Set.Make (Int) in
  let visited_decisions = Hashtbl.create 251 in
  let reachable_variables = ref Int_set.empty in
  let rec visit_decision id =
    if not (Hashtbl.mem visited_decisions id) then begin
      Hashtbl.add visited_decisions id ();
      match Circuit_dd.lookup lowered.decisions id with
      | Circuit_dd.Leaf _ -> ()
      | Circuit_dd.Choice (variable, children) ->
          reachable_variables := Int_set.add variable !reachable_variables;
          Array.iter visit_decision children
    end
  in
  List.iter visit_decision lowered.result_parts;
  let reachable_random_variables =
    Int_set.cardinal !reachable_variables
  in
  let stats =
    { random_variables = Hashtbl.length lowered.choices
    ; reachable_random_variables
    ; additive_terms = lowered.additive_terms
    ; decision_nodes = Circuit_dd.node_count lowered.decisions
    ; eliminated_decision_nodes = eliminated.eliminated_dd_nodes
    ; arithmetic_nodes = Circuit_ir.node_count lowered.arithmetic
    ; reachable_arithmetic_nodes =
        Circuit_ir.reachable_count lowered.arithmetic eliminated.root
    }
  in
  { expression
  ; arithmetic = lowered.arithmetic
  ; root = eliminated.root
  ; stats
  }

let to_expr compiled = compiled.expression

let compile_expr typed_expression =
  to_expr (compile typed_expression)

let eval compiled assignments =
  Circuit_runtime.eval compiled.arithmetic compiled.root assignments
