(** Algebraic symbolic terms. Sample identities are distinct from parameter names. *)
type op = Add | Sub | Mul | Div | Lt | Le | Eq
type term =
  | Number of float | Boolean of bool | Parameter of string
  | Sample of int | Finite of int * int
  | Binary of op * term * term | Not of term | Is_integer of term

let negate = function
  | Boolean b -> Boolean (not b)
  | Not t -> t
  | t -> Not t

let binary op a b =
  match op, a, b with
  | Add, Number x, Number y -> Number (x +. y)
  | Sub, Number x, Number y -> Number (x -. y)
  | Mul, Number x, Number y -> Number (x *. y)
  | Div, Number x, Number y when y <> 0. -> Number (x /. y)
  | Lt, Number x, Number y -> Boolean (x < y)
  | Le, Number x, Number y -> Boolean (x <= y)
  | Eq, Number x, Number y -> Boolean (x = y)
  | Eq, Boolean x, Boolean y -> Boolean (x = y)
  | Eq, Finite (x,n), Finite (y,m) when n=m -> Boolean (x=y)
  | (Eq | Le), x, y when x=y -> Boolean true
  | Lt, x, y when x=y -> Boolean false
  | Add, Number 0., x | Add, x, Number 0. -> x
  | Sub, x, Number 0. -> x
  | Mul, Number 1., x | Mul, x, Number 1. -> x
  | Div, x, Number 1. -> x
  | _ -> Binary (op,a,b)

let is_integer = function
  | Number n -> Boolean (Float.is_integer n)
  | t -> Is_integer t

let op_string = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
  | Lt -> "<" | Le -> "<=" | Eq -> "="

let rec to_string = function
  | Number n -> Printf.sprintf "%.17g" n
  | Boolean b -> string_of_bool b
  | Parameter s -> s
  | Sample id -> Printf.sprintf "sample#%d" id
  | Finite (k,n) -> Printf.sprintf "%d#%d" k n
  | Binary (op,a,b) ->
      Printf.sprintf "(%s %s %s)" (to_string a) (op_string op) (to_string b)
  | Not (Binary (Lt,a,b)) -> Printf.sprintf "(%s >= %s)" (to_string a) (to_string b)
  | Not (Binary (Le,a,b)) -> Printf.sprintf "(%s > %s)" (to_string a) (to_string b)
  | Not (Binary (Eq,a,b)) -> Printf.sprintf "(%s != %s)" (to_string a) (to_string b)
  | Not t -> "not " ^ to_string t
  | Is_integer t -> "is_integer(" ^ to_string t ^ ")"

let rec samples = function
  | Sample id -> [id]
  | Binary (_,a,b) -> List.sort_uniq compare (samples a @ samples b)
  | Not t | Is_integer t -> samples t
  | Number _ | Boolean _ | Parameter _ | Finite _ -> []

let is_boolean = function
  | Boolean _ | Not _ | Is_integer _ | Binary ((Lt | Le | Eq),_,_) -> true
  | _ -> false

let finite_number = function
  | Number n -> (match classify_float n with FP_nan | FP_infinite -> false | _ -> true)
  | _ -> true

(** Replace [Sample id] by [value], re-simplifying on the way up. *)
let rec substitute id value = function
  | Sample k when k=id -> value
  | Binary (op,a,b) -> binary op (substitute id value a) (substitute id value b)
  | Not t -> negate (substitute id value t)
  | Is_integer t -> is_integer (substitute id value t)
  | t -> t
