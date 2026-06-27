module StringSet = Set.Make(String)

let var_counter = ref 0
let fresh_var (prefix : string) : string =
  incr var_counter;
  prefix ^ string_of_int !var_counter

let gen_let (base_name_hint : string) (rhs_expr : Ast.expr) (body_fn : string -> Ast.expr) : Ast.expr =
  match rhs_expr with
  | Ast.ExprNode (Ast.Var existing_var_name) ->
      body_fn existing_var_name
  | _ ->
      let new_var_name = fresh_var base_name_hint in
      Ast.ExprNode (Ast.Let (new_var_name, rhs_expr, body_fn new_var_name))

let bit_length n =
  if n < 0 then invalid_arg "bit_length: only non-negative integers allowed"
  else if n = 0 then 1
  else
    let rec aux n acc =
      if n = 0 then acc
      else aux (n lsr 1) (acc + 1)
    in
    aux n 0

(* For getting the correct int size in the to_dice conversion *)
let curr_max_int_sz = ref 0

let expr_list xs =
  List.fold_right
    (fun x acc -> Ast.ExprNode (Ast.Cons (x, acc)))
    xs
    (Ast.ExprNode Ast.Nil)

let is_float_ty ty =
  match Ast.force ty with
  | Ast.TFloat _ -> true
  | _ -> false

let free_float_vars te =
  (* Walks the typed AST and collects free variables whose type is float,
     ignoring locally bound variables. *)
  let rec sample bound = function
    | Ast.Distr1 (_, e1) -> expr bound e1
    | Ast.Distr2 (_, e1, e2) -> StringSet.union (expr bound e1) (expr bound e2)
  and union_many sets =
    List.fold_left StringSet.union StringSet.empty sets
  and expr bound (ty, _, Ast.TAExprNode ae) =
    match ae with
    | Ast.Var x ->
        if is_float_ty ty && not (StringSet.mem x bound) then StringSet.singleton x
        else StringSet.empty
    | Ast.Const _ | Ast.BoolConst _ | Ast.FinConst _ | Ast.Nil | Ast.Unit
    | Ast.RuntimeError _ ->
        StringSet.empty
    | Ast.Let (x, e1, e2) ->
        StringSet.union (expr bound e1) (expr (StringSet.add x bound) e2)
    | Ast.Fun (x, e1) -> expr (StringSet.add x bound) e1
    | Ast.Fix (f, x, e1) -> expr (StringSet.add f (StringSet.add x bound)) e1
    | Ast.MatchList (e1, e_nil, y, ys, e_cons) ->
        union_many
          [ expr bound e1
          ; expr bound e_nil
          ; expr (StringSet.add y (StringSet.add ys bound)) e_cons
          ]
    | Ast.Sample dist -> sample bound dist
    | Ast.Cdf (dist, point) -> StringSet.union (sample bound dist) (expr bound point)
    | Ast.DiscreteCase cases ->
        union_many
          (List.map
             (fun (branch, prob) -> StringSet.union (expr bound branch) (expr bound prob))
             cases)
    | Ast.Add (e1, e2) | Ast.Sub (e1, e2) | Ast.Mul (e1, e2)
    | Ast.Div (e1, e2) | Ast.Cmp (_, e1, e2, _)
    | Ast.FinCmp (_, e1, e2, _, _) | Ast.FinEq (e1, e2, _)
    | Ast.And (e1, e2) | Ast.Or (e1, e2) | Ast.Pair (e1, e2)
    | Ast.FuncApp (e1, e2) | Ast.Cons (e1, e2) | Ast.Assign (e1, e2)
    | Ast.Seq (e1, e2) ->
        StringSet.union (expr bound e1) (expr bound e2)
    | Ast.Not e1 | Ast.First e1 | Ast.Second e1 | Ast.Observe e1
    | Ast.Ref e1 | Ast.Deref e1 ->
        expr bound e1
    | Ast.Reset e1 -> expr bound e1
    | Ast.Shift (k, e1) -> expr (StringSet.add k bound) e1
    | Ast.If (e1, e2, e3) ->
        union_many [expr bound e1; expr bound e2; expr bound e3]
    | Ast.CdfExpr (kernel, point) ->
        StringSet.union (expr bound kernel) (expr bound point)
    | Ast.SpecialFunc (_, args) -> union_many (List.map (expr bound) args)
  in
  expr StringSet.empty te
