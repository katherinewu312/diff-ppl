open Ast

type at =
  { param : string
  ; value : float
  }

type idx_value =
  | IVConst of float
  | IVSym of string * expr

module StringMap = Map.Make(String)

let find_index pred lst =
  let rec loop i = function
    | [] -> None
    | x :: xs -> if pred x then Some i else loop (i + 1) xs
  in
  loop 0 lst

let rec eval_bool_env env (ExprNode e) : bool option =
  match e with
  | BoolConst b -> Some b
  | Cmp (op, e1, e2, _) ->
      (match eval_float_env env e1, eval_float_env env e2 with
       | Some f1, Some f2 ->
           Some
             (match op with
              | Lt -> f1 < f2
              | Le -> f1 <= f2)
       | _ -> None)
  | And (e1, e2) ->
      (match eval_bool_env env e1 with
       | Some false -> Some false
       | Some true -> eval_bool_env env e2
       | None -> None)
  | Or (e1, e2) ->
      (match eval_bool_env env e1 with
       | Some true -> Some true
       | Some false -> eval_bool_env env e2
       | None -> None)
  | Not e1 ->
      Option.map not (eval_bool_env env e1)
  | If (cond, e_then, e_else) ->
      (match eval_bool_env env cond with
       | Some true -> eval_bool_env env e_then
       | Some false -> eval_bool_env env e_else
       | None -> None)
  | Let (x, e1, e2) ->
      (match eval_float_env env e1 with
       | Some f -> eval_bool_env (StringMap.add x f env) e2
       | None -> None)
  | _ -> None

and eval_float_env env (ExprNode e) : float option =
  match e with
  | Const f -> Some f
  | Var x -> StringMap.find_opt x env
  | Add (e1, e2) ->
      (match eval_float_env env e1, eval_float_env env e2 with
       | Some f1, Some f2 -> Some (f1 +. f2)
       | _ -> None)
  | Sub (e1, e2) ->
      (match eval_float_env env e1, eval_float_env env e2 with
       | Some f1, Some f2 -> Some (f1 -. f2)
       | _ -> None)
  | Mul (e1, e2) ->
      (match eval_float_env env e1, eval_float_env env e2 with
       | Some f1, Some f2 -> Some (f1 *. f2)
       | _ -> None)
  | Div (e1, e2) ->
      (match eval_float_env env e1, eval_float_env env e2 with
       | Some _, Some 0.0 -> None
       | Some f1, Some f2 -> Some (f1 /. f2)
       | _ -> None)
  | If (cond, e_then, e_else) ->
      (match eval_bool_env env cond with
       | Some true -> eval_float_env env e_then
       | Some false -> eval_float_env env e_else
       | None -> None)
  | Let (x, e1, e2) ->
      (match eval_float_env env e1 with
       | Some f -> eval_float_env (StringMap.add x f env) e2
       | None -> None)
  | _ -> None

let cut_value_expr = function
  | CVConst f -> ExprNode (Const f)
  | CVSym (_, e) -> e

let eval_cut_value_at (at : at) (cv : cut_val) : float =
  let env = StringMap.singleton at.param at.value in
  match eval_float_env env (cut_value_expr cv) with
  | Some f -> f
  | None ->
      failwith
        ("Cannot order symbolic cut "
         ^ Pretty.string_of_expr_plain (cut_value_expr cv)
         ^ " at "
         ^ at.param
         ^ "="
         ^ string_of_float at.value)

let ordered_cuts ?at (cut_set : CutSet.t) : cut list =
  let cuts = CutSet.elements cut_set in
  match at with
  | None -> cuts
  | Some at ->
      let cut_value = function
        | Less cv | LessEq cv -> eval_cut_value_at at cv
      in
      List.sort
        (fun c1 c2 ->
           let by_value = compare (cut_value c1) (cut_value c2) in
           if by_value <> 0 then by_value else compare_cut c1 c2)
        cuts

let eval_idx_value_at (at : at) = function
  | IVConst f -> f
  | IVSym (_, e) ->
      (match eval_float_env (StringMap.singleton at.param at.value) e with
       | Some f -> f
       | None ->
           failwith
             ("Cannot order symbolic value "
              ^ Pretty.string_of_expr_plain e
              ^ " at "
              ^ at.param
              ^ "="
              ^ string_of_float at.value))

let satisfies_cut ?at (iv : idx_value) (cut : cut) : bool =
  match at with
  | Some at ->
      let f = eval_idx_value_at at iv in
      let cut_value = function
        | Less cv | LessEq cv -> eval_cut_value_at at cv
      in
      (match cut with
       | Less _ -> f < cut_value cut
       | LessEq _ -> f <= cut_value cut)
  | None ->
      (match iv, cut with
       | IVConst f, Less (CVConst c) -> f < c
       | IVConst f, LessEq (CVConst c) -> f <= c
       | IVSym _, Less (CVSym _) -> false
       | IVSym (s, _), LessEq (CVSym (s', _)) -> s = s'
       | _ -> false)

let idx_and_modulus ?at (iv : idx_value) (cut_set : CutSet.t) : int * int =
  let cuts = ordered_cuts ?at cut_set in
  let modulus = 1 + List.length cuts in
  let idx =
    match find_index (satisfies_cut ?at iv) cuts with
    | Some i -> i
    | None -> modulus - 1
  in
  (idx, modulus)
