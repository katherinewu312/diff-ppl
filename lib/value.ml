(** Runtime values produced by symbolic execution. *)
type t =
  | Scalar of Symbolic.term
  | Pair of t * t
  | Nil | Cons of t * t
  | Unit
  | Location of int
  | Closure of closure
and closure = {
  self : string option;  (** bound to the closure itself, for [fix] *)
  param : string;
  body : Ast.expr;
  env : env;
}
and env = (string * t) list

let rec to_string = function
  | Scalar t -> Symbolic.to_string t
  | Pair (a,b) -> "(" ^ to_string a ^ ", " ^ to_string b ^ ")"
  | Nil -> "nil"
  | Cons (a,b) -> "(" ^ to_string a ^ " :: " ^ to_string b ^ ")"
  | Unit -> "()"
  | Location id -> Printf.sprintf "ref#%d" id
  | Closure {self=None; param; _} -> "<closure " ^ param ^ ">"
  | Closure {self=Some name; param; _} -> "<recursive closure " ^ name ^ " " ^ param ^ ">"
