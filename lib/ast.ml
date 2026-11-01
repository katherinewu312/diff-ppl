(** Source syntax only *)
type arith = Add | Sub | Mul | Div
type comparison = Lt | Le | Eq

type distribution = Uniform | Gaussian
  | Unsupported_distribution of string

let distribution_name = function
  | Uniform -> "uniform" | Gaussian -> "gaussian" | Unsupported_distribution name -> name

let distribution_of_name = function
  | "uniform" -> Some Uniform
  | "gaussian" | "normal" -> Some Gaussian
  | ("flip" | "discrete" | "beta" | "gamma" | "exponential" | "binomial"
    | "poisson" | "lognormal" | "laplace" | "cauchy" | "weibull" | "tdist"
    | "chi2" | "logistic" | "rayleigh" | "pareto" | "gumbel1" | "gumbel2"
    | "exppow") as name -> Some (Unsupported_distribution name)
  | _ -> None

type expr =
  | Var of string
  | Const of string
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
  | Fix of string * string * expr                    (** Recursive closure; [let rec f = fun x -> body] desugars to [Let (f, Fix (f,x,body), ...)]. *)
  | Apply of expr * expr
  | Pair of expr * expr | First of expr | Second of expr
  | Nil | Cons of expr * expr
  | Match_list of expr * expr * string * string * expr
  | Ref of expr | Deref of expr | Assign of expr * expr | Seq of expr * expr
  | Sample of distribution * expr list
  | Observe of expr

(** The CLI supplies the free inputs in the initial Gamma. *)
module Names = Set.Make(String)
let rec free_variables = function
  | Var x -> Names.singleton x
  | Const _ | Bool _ | Unit | Finite _ | Nil -> Names.empty
  | Let (x,a,b) -> Names.union (free_variables a) (Names.remove x (free_variables b))
  | Fun (x,b) -> Names.remove x (free_variables b)
  | Fix (f,x,b) -> Names.remove f (Names.remove x (free_variables b))
  | If (c,a,b) -> Names.union (free_variables c) (Names.union (free_variables a) (free_variables b))
  | Match_list (e,nil,x,xs,cons) -> Names.union (free_variables e)
      (Names.union (free_variables nil) (Names.remove x (Names.remove xs (free_variables cons))))
  | Arith (_,a,b) | Compare (_,a,b) | Finite_compare (_,_,a,b)
  | And (a,b) | Or (a,b) | Apply (a,b) | Pair (a,b) | Cons (a,b)
  | Assign (a,b) | Seq (a,b) -> Names.union (free_variables a) (free_variables b)
  | Not e | First e | Second e | Ref e | Deref e | Observe e -> free_variables e
  | Sample (_,args) -> List.fold_left (fun s e -> Names.union s (free_variables e)) Names.empty args

let rec to_string expression =
  let pair op a b = "(" ^ to_string a ^ " " ^ op ^ " " ^ to_string b ^ ")" in
  match expression with
  | Var x -> x | Const n -> n | Bool b -> string_of_bool b | Unit -> "()" | Nil -> "nil"
  | Finite (i,n) -> Printf.sprintf "%d#%d" i n
  | Arith (op,a,b) -> pair (match op with Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/") a b
  | Compare (op,a,b) -> pair (match op with Lt -> "<" | Le -> "<=" | Eq -> "=") a b
  | Finite_compare (op,n,a,b) -> pair ((match op with Lt -> "<" | Le -> "<=" | Eq -> "==") ^ "#" ^ string_of_int n) a b
  | And (a,b) -> pair "&&" a b | Or (a,b) -> pair "||" a b | Not e -> "not (" ^ to_string e ^ ")"
  | If (c,a,b) -> "(if " ^ to_string c ^ " then " ^ to_string a ^ " else " ^ to_string b ^ ")"
  | Let (f,Fix (self,x,body),rest) when self=f ->
      "(let rec " ^ f ^ " = fun " ^ x ^ " -> " ^ to_string body ^ " in " ^ to_string rest ^ ")"
  | Let (x,a,b) -> "(let " ^ x ^ " = " ^ to_string a ^ " in " ^ to_string b ^ ")"
  | Fun (x,e) -> "(fun " ^ x ^ " -> " ^ to_string e ^ ")"
  | Fix (f,x,e) -> "(fix " ^ f ^ " " ^ x ^ " := " ^ to_string e ^ ")"
  | Apply (f,a) -> pair "" f a
  | Pair (a,b) -> "(" ^ to_string a ^ ", " ^ to_string b ^ ")"
  | Cons (a,b) -> pair "::" a b | First e -> "fst (" ^ to_string e ^ ")"
  | Second e -> "snd (" ^ to_string e ^ ")"
  | Match_list (e,nil,x,xs,cons) -> "(match " ^ to_string e ^ " with nil -> " ^ to_string nil
      ^ " | " ^ x ^ " :: " ^ xs ^ " -> " ^ to_string cons ^ " end)"
  | Ref e -> "ref (" ^ to_string e ^ ")" | Deref e -> "!(" ^ to_string e ^ ")"
  | Assign (a,b) -> pair ":=" a b | Seq (a,b) -> pair ";" a b
  | Sample (d,args) -> distribution_name d ^ "(" ^ String.concat ", " (List.map to_string args) ^ ")"
  | Observe e -> "observe (" ^ to_string e ^ ")"
