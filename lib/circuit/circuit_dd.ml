(** Reduced, ordered, multi-valued decision diagrams.

    Leaves refer to nodes in an arithmetic circuit.  A [Choice (q, xs)] node
    selects [xs.(i)] when random variable [q] has value [i].  Random-variable
    identifiers determine the ordering: identifiers increase along every path.

    Both leaves and choices are hash-consed.  In addition, [choice] implements
    the reduction rule [Choice (q, [d; ...; d]) = d]. *)

type ac_id = Circuit_ir.ac_id
type rv_id = int
type dd_id = int

type dd_node =
  | Leaf of ac_id
  | Choice of rv_id * dd_id array

module Node_key = struct
  type t = dd_node

  let array_equal left right =
    let length = Array.length left in
    length = Array.length right
    &&
    let rec loop index =
      index = length
      || (left.(index) = right.(index) && loop (index + 1))
    in
    loop 0

  let equal left right =
    match (left, right) with
    | Leaf x, Leaf y -> x = y
    | Choice (q, xs), Choice (r, ys) -> q = r && array_equal xs ys
    | Leaf _, Choice _ | Choice _, Leaf _ -> false

  let hash = Hashtbl.hash
end

module Node_table = Hashtbl.Make (Node_key)

module Unary_cache = Hashtbl.Make (struct
  type t = int * dd_id

  let equal = ( = )
  let hash = Hashtbl.hash
end)

module Binary_cache = Hashtbl.Make (struct
  type t = int * dd_id * dd_id

  let equal = ( = )
  let hash = Hashtbl.hash
end)

module Triple_cache = Hashtbl.Make (struct
  type t = dd_id * dd_id * dd_id

  let equal = ( = )
  let hash = Hashtbl.hash
end)

type t = {
  nodes : (dd_id, dd_node) Hashtbl.t;
  unique : dd_id Node_table.t;
  arities : (rv_id, int) Hashtbl.t;
  unary_cache : dd_id Unary_cache.t;
  binary_cache : dd_id Binary_cache.t;
  mutable next_id : dd_id;
  mutable next_rv : rv_id;
}

let create ?(capacity = 251) () =
  {
    nodes = Hashtbl.create capacity;
    unique = Node_table.create capacity;
    arities = Hashtbl.create 31;
    unary_cache = Unary_cache.create capacity;
    binary_cache = Binary_cache.create capacity;
    next_id = 0;
    next_rv = 0;
  }

let node_count manager = manager.next_id
let rv_count manager = Hashtbl.length manager.arities

let lookup_internal manager id =
  match Hashtbl.find_opt manager.nodes id with
  | Some node -> node
  | None -> invalid_arg ("Circuit_dd: unknown DD node " ^ string_of_int id)

(** Return a node without exposing the mutable array stored in the unique
    table. *)
let lookup manager id =
  match lookup_internal manager id with
  | Leaf value -> Leaf value
  | Choice (variable, children) -> Choice (variable, Array.copy children)

let intern manager node =
  match Node_table.find_opt manager.unique node with
  | Some id -> id
  | None ->
      let id = manager.next_id in
      manager.next_id <- id + 1;
      (* Arrays used as hash-table keys must never subsequently be mutated. *)
      let stored =
        match node with
        | Leaf value -> Leaf value
        | Choice (variable, children) ->
            Choice (variable, Array.copy children)
      in
      Node_table.add manager.unique stored id;
      Hashtbl.add manager.nodes id stored;
      id

let leaf manager value = intern manager (Leaf value)

let register_rv manager variable arity =
  if variable < 0 then invalid_arg "Circuit_dd.register_rv: negative variable";
  if arity <= 0 then invalid_arg "Circuit_dd.register_rv: empty domain";
  (match Hashtbl.find_opt manager.arities variable with
  | None -> Hashtbl.add manager.arities variable arity
  | Some previous when previous = arity -> ()
  | Some previous ->
      invalid_arg
        (Printf.sprintf
           "Circuit_dd: variable %d used with arities %d and %d"
           variable previous arity));
  if variable >= manager.next_rv then manager.next_rv <- variable + 1

let fresh_rv manager ~arity =
  let variable = manager.next_rv in
  manager.next_rv <- variable + 1;
  register_rv manager variable arity;
  variable

let arity manager variable =
  match Hashtbl.find_opt manager.arities variable with
  | Some value -> value
  | None ->
      invalid_arg
        ("Circuit_dd: unknown random variable " ^ string_of_int variable)

let top_variable manager id =
  match lookup_internal manager id with
  | Leaf _ -> None
  | Choice (variable, _) -> Some variable

let all_identical children =
  let first = children.(0) in
  let rec loop index =
    index = Array.length children
    || (children.(index) = first && loop (index + 1))
  in
  loop 1

let choice manager variable children =
  let child_count = Array.length children in
  register_rv manager variable child_count;
  (* Check IDs even when the choice reduces away. *)
  Array.iter (fun child -> ignore (lookup_internal manager child)) children;
  if all_identical children then children.(0)
  else (
    Array.iter
      (fun child ->
        match top_variable manager child with
        | Some child_variable when child_variable <= variable ->
            invalid_arg
              (Printf.sprintf
                 "Circuit_dd.choice: variable order violation (%d below %d)"
                 child_variable variable)
        | None | Some _ -> ())
      children;
    intern manager (Choice (variable, children)))

(** Operations carry fresh keys so their memo tables cannot accidentally mix
    (for example) addition and multiplication.  Retain and reuse an operation
    value to retain cached [map]/[apply2] results across calls. *)
type unary_op = {
  unary_key : int;
  unary_apply : ac_id -> ac_id;
}

type binary_op = {
  binary_key : int;
  binary_apply : ac_id -> ac_id -> ac_id;
}

let next_operation_key = ref 0

let fresh_operation_key () =
  let key = !next_operation_key in
  next_operation_key := key + 1;
  key

let make_unary apply =
  { unary_key = fresh_operation_key (); unary_apply = apply }

let make_binary apply =
  { binary_key = fresh_operation_key (); binary_apply = apply }

let map manager operation root =
  let rec visit id =
    let cache_key = (operation.unary_key, id) in
    match Unary_cache.find_opt manager.unary_cache cache_key with
    | Some result -> result
    | None ->
        let result =
          match lookup_internal manager id with
          | Leaf value -> leaf manager (operation.unary_apply value)
          | Choice (variable, children) ->
              choice manager variable (Array.map visit children)
        in
        Unary_cache.add manager.unary_cache cache_key result;
        result
  in
  visit root

let apply2 manager operation left_root right_root =
  let rec visit left right =
    let cache_key = (operation.binary_key, left, right) in
    match Binary_cache.find_opt manager.binary_cache cache_key with
    | Some result -> result
    | None ->
        let result =
          match (lookup_internal manager left, lookup_internal manager right) with
          | Leaf x, Leaf y -> leaf manager (operation.binary_apply x y)
          | Choice (q, xs), Choice (r, ys) when q = r ->
              if Array.length xs <> Array.length ys then
                invalid_arg
                  (Printf.sprintf
                     "Circuit_dd.apply2: inconsistent arity for variable %d" q);
              choice manager q
                (Array.init (Array.length xs) (fun index ->
                     visit xs.(index) ys.(index)))
          | Choice (q, xs), Choice (r, _) when q < r ->
              choice manager q (Array.map (fun child -> visit child right) xs)
          | Choice _, Choice (r, ys) ->
              choice manager r (Array.map (fun child -> visit left child) ys)
          | Choice (q, xs), Leaf _ ->
              choice manager q (Array.map (fun child -> visit child right) xs)
          | Leaf _, Choice (r, ys) ->
              choice manager r (Array.map (fun child -> visit left child) ys)
        in
        Binary_cache.add manager.binary_cache cache_key result;
        result
  in
  visit left_root right_root

(** One-off variants are convenient during lowering.  The operation is still
    memoized throughout this traversal; use [make_unary]/[make_binary] directly
    when the cache should be shared by several calls. *)
let map_once manager apply root = map manager (make_unary apply) root

let apply2_once manager apply left right =
  apply2 manager (make_binary apply) left right

let minimum_variable first second =
  match (first, second) with
  | None, value | value, None -> value
  | Some x, Some y -> Some (min x y)

let branch_at manager variable index id =
  match lookup_internal manager id with
  | Choice (top, children) when top = variable -> children.(index)
  | Leaf _ | Choice _ -> id

(** Conditional selection over three DDs.  [truth] must recognize boolean AC
    leaves and return [Some true] or [Some false].  A non-boolean condition leaf
    is rejected. *)
let ite_with manager ~truth condition if_true if_false =
  let memo = Triple_cache.create 251 in
  let rec visit condition if_true if_false =
    if if_true = if_false then if_true
    else
      let cache_key = (condition, if_true, if_false) in
      match Triple_cache.find_opt memo cache_key with
      | Some result -> result
      | None ->
          let result =
            match lookup_internal manager condition with
            | Leaf value -> (
                match truth value with
                | Some true -> if_true
                | Some false -> if_false
                | None ->
                    invalid_arg
                      "Circuit_dd.ite: condition is not a constant boolean")
            | Choice _ ->
                let top =
                  minimum_variable (top_variable manager condition)
                    (minimum_variable (top_variable manager if_true)
                       (top_variable manager if_false))
                in
                let variable =
                  match top with
                  | Some variable -> variable
                  | None -> assert false
                in
                let variable_arity = arity manager variable in
                choice manager variable
                  (Array.init variable_arity (fun index ->
                       visit
                         (branch_at manager variable index condition)
                         (branch_at manager variable index if_true)
                         (branch_at manager variable index if_false)))
          in
          Triple_cache.add memo cache_key result;
          result
  in
  visit condition if_true if_false

(** Initial circuit lowering encodes booleans as the AC constants zero and one.
    Deterministic, non-constant conditions are intentionally unsupported. *)
let ite manager arithmetic condition if_true if_false =
  let truth id =
    match Circuit_ir.lookup arithmetic id with
    | Circuit_ir.Const value when value = 0.0 -> Some false
    | Circuit_ir.Const value when value = 1.0 -> Some true
    | Circuit_ir.Const _ | Circuit_ir.Param _ | Circuit_ir.Add _
    | Circuit_ir.Sub _ | Circuit_ir.Mul _ | Circuit_ir.Div _
    | Circuit_ir.Special _ -> None
  in
  ite_with manager ~truth condition if_true if_false

let clear_operation_caches manager =
  Unary_cache.clear manager.unary_cache;
  Binary_cache.clear manager.binary_cache

(** Reachable DD nodes in increasing ID order.  Since a choice is interned
    after its children, this is also a children-before-parent order. *)
let reachable manager root =
  let seen = Hashtbl.create 31 in
  let rec visit id =
    if not (Hashtbl.mem seen id) then (
      Hashtbl.add seen id ();
      match lookup_internal manager id with
      | Leaf _ -> ()
      | Choice (_, children) -> Array.iter visit children)
  in
  visit root;
  Hashtbl.fold (fun id () ids -> id :: ids) seen [] |> List.sort compare

let support manager root =
  let variables = Hashtbl.create 17 in
  List.iter
    (fun id ->
      match lookup_internal manager id with
      | Leaf _ -> ()
      | Choice (variable, _) -> Hashtbl.replace variables variable ())
    (reachable manager root);
  Hashtbl.fold (fun variable () result -> variable :: result) variables []
  |> List.sort compare
