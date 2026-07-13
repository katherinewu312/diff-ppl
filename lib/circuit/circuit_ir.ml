(** Hash-consed arithmetic circuits.

    An [ac_id] names a node owned by one manager.  Nodes may only refer to
    nodes that were already inserted into the same manager, so node IDs are
    also a topological order.  Clients should construct nodes with the smart
    constructors below rather than constructing [ac_node] values directly.

    Arrays in [Special] are treated as immutable.  Both [special] and
    [lookup] copy those arrays at the manager boundary. *)

type ac_id = int

type ac_node =
  | Const of float
  | Param of string
  | Add of ac_id * ac_id
  | Sub of ac_id * ac_id
  | Mul of ac_id * ac_id
  | Div of ac_id * ac_id
  | Special of string * ac_id array

let float_equal x y =
  Int64.bits_of_float x = Int64.bits_of_float y

let array_equal xs ys =
  let n = Array.length xs in
  if n <> Array.length ys then false
  else
    let rec loop i =
      i = n || (xs.(i) = ys.(i) && loop (i + 1))
    in
    loop 0

let node_equal x y =
  match x, y with
  | Const a, Const b -> float_equal a b
  | Param a, Param b -> String.equal a b
  | Add (a1, a2), Add (b1, b2)
  | Sub (a1, a2), Sub (b1, b2)
  | Mul (a1, a2), Mul (b1, b2)
  | Div (a1, a2), Div (b1, b2) ->
      a1 = b1 && a2 = b2
  | Special (name1, args1), Special (name2, args2) ->
      String.equal name1 name2 && array_equal args1 args2
  | _ -> false

let hash_combine x y =
  (x * 65599) lxor y

let node_hash = function
  | Const value ->
      hash_combine 1 (Hashtbl.hash (Int64.bits_of_float value))
  | Param name ->
      hash_combine 2 (Hashtbl.hash name)
  | Add (left, right) ->
      hash_combine (hash_combine 3 left) right
  | Sub (left, right) ->
      hash_combine (hash_combine 4 left) right
  | Mul (left, right) ->
      hash_combine (hash_combine 5 left) right
  | Div (left, right) ->
      hash_combine (hash_combine 6 left) right
  | Special (name, args) ->
      Array.fold_left hash_combine
        (hash_combine 7 (Hashtbl.hash name))
        args

module Node_table = Hashtbl.Make(struct
  type t = ac_node
  let equal = node_equal
  let hash = node_hash
end)

type t =
  { index : ac_id Node_table.t
  ; mutable nodes : ac_node array
  ; mutable length : int
  }

type manager = t

let create ?(initial_capacity = 64) () =
  if initial_capacity < 0 then
    invalid_arg "Circuit_ir.create: negative initial capacity";
  let capacity = max 1 initial_capacity in
  { index = Node_table.create capacity
  ; nodes = Array.make capacity (Const 0.0)
  ; length = 0
  }

let node_count manager = manager.length

let valid_id manager id =
  id >= 0 && id < manager.length

let require_id manager id =
  if not (valid_id manager id) then
    invalid_arg
      (Printf.sprintf
         "Circuit_ir: node ID %d does not belong to this manager" id)

let copy_node = function
  | Special (name, args) -> Special (name, Array.copy args)
  | node -> node

let node_at manager id =
  require_id manager id;
  Array.unsafe_get manager.nodes id

let lookup manager id =
  copy_node (node_at manager id)

let ensure_capacity manager =
  if manager.length = Array.length manager.nodes then begin
    let old_capacity = Array.length manager.nodes in
    let new_capacity = max 1 (old_capacity * 2) in
    let new_nodes = Array.make new_capacity (Const 0.0) in
    Array.blit manager.nodes 0 new_nodes 0 manager.length;
    manager.nodes <- new_nodes
  end

let intern_raw manager node =
  let node = copy_node node in
  match Node_table.find_opt manager.index node with
  | Some id -> id
  | None ->
      ensure_capacity manager;
      let id = manager.length in
      manager.nodes.(id) <- node;
      manager.length <- id + 1;
      Node_table.add manager.index node id;
      id

let const manager value =
  (* Treat the two IEEE zero encodings as the same arithmetic constant. *)
  let value = if value = 0.0 then 0.0 else value in
  intern_raw manager (Const value)

let param manager name =
  intern_raw manager (Param name)

let const_value manager id =
  match node_at manager id with
  | Const value -> Some value
  | _ -> None

let is_zero manager id =
  match const_value manager id with
  | Some value -> value = 0.0
  | None -> false

let is_one manager id =
  match const_value manager id with
  | Some value -> value = 1.0
  | None -> false

let ordered_pair left right =
  if left <= right then left, right else right, left

let add manager left right =
  require_id manager left;
  require_id manager right;
  match const_value manager left, const_value manager right with
  | Some x, Some y -> const manager (x +. y)
  | Some x, _ when x = 0.0 -> right
  | _, Some y when y = 0.0 -> left
  | _ ->
      let left, right = ordered_pair left right in
      intern_raw manager (Add (left, right))

let sub manager left right =
  require_id manager left;
  require_id manager right;
  match const_value manager left, const_value manager right with
  | Some x, Some y -> const manager (x -. y)
  | _, Some y when y = 0.0 -> left
  | _ -> intern_raw manager (Sub (left, right))

let mul manager left right =
  require_id manager left;
  require_id manager right;
  match const_value manager left, const_value manager right with
  | Some x, Some y -> const manager (x *. y)
  | Some x, _ when x = 1.0 -> right
  | _, Some y when y = 1.0 -> left
  | Some x, _ when x = -1.0 -> sub manager (const manager 0.0) right
  | _, Some y when y = -1.0 -> sub manager (const manager 0.0) left
  | _ ->
      let left, right = ordered_pair left right in
      intern_raw manager (Mul (left, right))

let div manager numerator denominator =
  require_id manager numerator;
  require_id manager denominator;
  match const_value manager numerator, const_value manager denominator with
  | Some x, Some y -> const manager (x /. y)
  | _, Some y when y = 1.0 -> numerator
  | _ -> intern_raw manager (Div (numerator, denominator))

let special manager name args =
  Array.iter (require_id manager) args;
  intern_raw manager (Special (name, args))

let sum manager nodes =
  let n = Array.length nodes in
  if n = 0 then const manager 0.0
  else begin
    Array.iter (require_id manager) nodes;
    let result = ref nodes.(0) in
    for i = 1 to n - 1 do
      result := add manager !result nodes.(i)
    done;
    !result
  end

let sum_list manager nodes =
  match nodes with
  | [] -> const manager 0.0
  | first :: rest ->
      require_id manager first;
      List.fold_left (add manager) first rest

let product manager nodes =
  let n = Array.length nodes in
  if n = 0 then const manager 1.0
  else begin
    Array.iter (require_id manager) nodes;
    let result = ref nodes.(0) in
    for i = 1 to n - 1 do
      result := mul manager !result nodes.(i)
    done;
    !result
  end

let children_of_node = function
  | Const _ | Param _ -> [||]
  | Add (left, right)
  | Sub (left, right)
  | Mul (left, right)
  | Div (left, right) -> [|left; right|]
  | Special (_, args) -> Array.copy args

let children manager id =
  children_of_node (node_at manager id)

let iter f manager =
  for id = 0 to manager.length - 1 do
    f id (lookup manager id)
  done

let fold f manager initial =
  let result = ref initial in
  for id = 0 to manager.length - 1 do
    result := f !result id (lookup manager id)
  done;
  !result

(** [reachable manager root] returns all nodes reachable from [root] in
    topological order (children before parents). *)
let reachable manager root =
  require_id manager root;
  let seen = Array.make manager.length false in
  let pending = Stack.create () in
  Stack.push root pending;
  while not (Stack.is_empty pending) do
    let id = Stack.pop pending in
    if not seen.(id) then begin
      seen.(id) <- true;
      Array.iter
        (fun child ->
           require_id manager child;
           if not seen.(child) then Stack.push child pending)
        (children_of_node (node_at manager id))
    end
  done;
  let result = ref [] in
  for id = manager.length - 1 downto 0 do
    if seen.(id) then result := id :: !result
  done;
  !result

let reachable_array manager root =
  Array.of_list (reachable manager root)

let reachable_count manager root =
  List.length (reachable manager root)

module String_set = Set.Make(String)

let is_operation = function
  | Add _ | Sub _ | Mul _ | Div _ | Special _ -> true
  | Const _ | Param _ -> false

(** Reify a circuit as a deterministic Slice expression.

    Every reachable operation is emitted as a topologically ordered [Let]
    binding.  Thus a shared circuit node is evaluated once rather than being
    expanded into an expression tree.  Constants and parameters remain
    atoms. *)
let reify manager root =
  let ids = reachable manager root in
  let used_names =
    List.fold_left
      (fun names id ->
         match node_at manager id with
         | Param name -> String_set.add name names
         | _ -> names)
      String_set.empty
      ids
  in
  let used_names = ref used_names in
  let binding_names = Array.make manager.length None in
  let fresh_binding_name id =
    let base = "_circuit_" ^ string_of_int id in
    let rec choose suffix =
      let candidate =
        if suffix = 0 then base
        else base ^ "_" ^ string_of_int suffix
      in
      if String_set.mem candidate !used_names then choose (suffix + 1)
      else begin
        used_names := String_set.add candidate !used_names;
        candidate
      end
    in
    choose 0
  in
  List.iter
    (fun id ->
       if is_operation (node_at manager id) then
         binding_names.(id) <- Some (fresh_binding_name id))
    ids;
  let node expression = Ast.ExprNode expression in
  let atom id =
    match node_at manager id with
    | Const value -> node (Ast.Const value)
    | Param name -> node (Ast.Var name)
    | Add _ | Sub _ | Mul _ | Div _ | Special _ ->
        (match binding_names.(id) with
         | Some name -> node (Ast.Var name)
         | None -> assert false)
  in
  let operation_expression id =
    match node_at manager id with
    | Add (left, right) -> node (Ast.Add (atom left, atom right))
    | Sub (left, right) -> node (Ast.Sub (atom left, atom right))
    | Mul (left, right) -> node (Ast.Mul (atom left, atom right))
    | Div (left, right) -> node (Ast.Div (atom left, atom right))
    | Special (name, args) ->
        node
          (Ast.SpecialFunc
             (name, Array.to_list (Array.map atom args)))
    | Const _ | Param _ ->
        invalid_arg "Circuit_ir.reify: expected an operation node"
  in
  let operations =
    List.filter (fun id -> is_operation (node_at manager id)) ids
  in
  List.fold_right
    (fun id body ->
       match binding_names.(id) with
       | Some name -> node (Ast.Let (name, operation_expression id, body))
       | None -> assert false)
    operations
    (atom root)

let to_expr = reify

let parameters manager root =
  List.fold_left
    (fun names id ->
       match node_at manager id with
       | Param name -> name :: names
       | _ -> names)
    []
    (List.rev (reachable manager root))
