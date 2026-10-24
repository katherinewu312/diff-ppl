(** Source syntax only *)
type arith = Add | Sub | Mul | Div
type comparison = Lt | Le | Eq

type expr =
  | Var of string
  | Const of float
  | Bool of bool
  | Unit
  | Finite of int * int                              (** [k#n], with 0 <= k < n *)
  | Arith of arith * expr * expr
  | Compare of comparison * expr * expr              (** on reals *)
  | Finite_compare of comparison * int * expr * expr (** on [_#n] values *)
  | And of expr * expr | Or of expr * expr | Not of expr
  | If of expr * expr * expr
  | Let of string * expr * expr
  | Fun of string * expr
  | Fix of string * string * expr                    (** [fix f x := body] *)
  | Apply of expr * expr
  | Pair of expr * expr | First of expr | Second of expr
  | Nil | Cons of expr * expr
  | Match_list of expr * expr * string * string * expr
  | Ref of expr | Deref of expr | Assign of expr * expr | Seq of expr * expr
  | Sample of Distribution.t * expr list
  | Observe of expr
