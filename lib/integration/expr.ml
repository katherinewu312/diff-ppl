(** Probability expressions: the result of integrating a path. They are
    functions of the program parameters, so they can be differentiated or
    evaluated later. Smart constructors fold constants. *)
type comparison = Lt | Le | Eq

type t =
  | Const of float
  | Param of string
  | Var of int  (** [sample#k], bound by an enclosing [Integral] *)
  | Add of t * t | Sub of t * t | Mul of t * t | Div of t * t
  | Min of t * t | Max of t * t
  | Exp of t | Erf of t | Ceil of t
  | Indicator of condition
  | Cdf of Distribution.t * t list * t  (** [P(X <= x)], no closed form used *)
  | Integral of integral
and condition =
  | Compare of comparison * t * t
  | Not of condition
  | Bool_param of string
(** [∫ density(x) * body dx] over [lower <= x <= upper] (a sum for
    integer-valued distributions); [None] is unbounded. *)
and integral = {
  var : int;
  distribution : Distribution.t;
  parameters : t list;
  lower : t option;
  upper : t option;
  body : t;
}

let zero = Const 0. and one = Const 1.

let rec neg = function
  | Const x -> Const (-. x)
  | Sub (Const 0., e) -> e
  | Sub (a,b) -> sub b a
  | e -> Sub (zero, e)
and add a b = match a,b with
  | Const x, Const y -> Const (x +. y)
  | Const 0., e | e, Const 0. -> e
  | e, Sub (Const 0., f) | Sub (Const 0., f), e -> sub e f
  | e, Const c when c < 0. -> Sub (e, Const (-. c))
  | _ -> Add (a,b)
and sub a b = match a,b with
  | Const x, Const y -> Const (x -. y)
  | e, Const 0. -> e
  | Const 0., e -> neg e
  | Const 1., Sub (Const 1., e) -> e
  | e, Const c when c < 0. -> add e (Const (-. c))
  | e, Sub (Const 0., f) -> add e f
  | _ when a = b -> zero
  | _ -> Sub (a,b)
let mul a b = match a,b with
  | Const x, Const y -> Const (x *. y)
  | Const 0., _ | _, Const 0. -> zero
  | Const 1., e | e, Const 1. -> e
  | Const (-1.), e | e, Const (-1.) -> neg e
  | _ -> Mul (a,b)
let rec div a b = match a,b with
  | Const x, Const y when y <> 0. -> Const (x /. y)
  | Const 0., _ -> zero
  | e, Const 1. -> e
  | e, Const (-1.) -> neg e
  | e, Const c when c < 0. -> div (neg e) (Const (-. c))
  | _ -> Div (a,b)
let unary f make = function Const x -> Const (f x) | e -> make e
let exp e = unary Float.exp (fun e -> Exp e) e
let erf e = unary Float.erf (fun e -> Erf e) e
let ceil e = unary Float.ceil (fun e -> Ceil e) e
let min a b = match a,b with
  | Const x, Const y -> Const (Float.min x y)
  | _ when a = b -> a
  | _ -> Min (a,b)
let max a b = match a,b with
  | Const x, Const y -> Const (Float.max x y)
  | _ when a = b -> a
  | _ -> Max (a,b)
let clamp e lo hi = min (max e lo) hi

let holds op x y = match op with Lt -> x < y | Le -> x <= y | Eq -> x = y
let rec indicator = function
  | Compare (op, Const x, Const y) -> Const (if holds op x y then 1. else 0.)
  | Not c -> (match indicator c with Const v -> Const (1. -. v) | _ -> Indicator (Not c))
  | c -> Indicator c

let integral i = if i.body = zero then zero else Integral i

let rec fold_children f acc = function
  | Const _ | Param _ | Var _ -> acc
  | Add (a,b) | Sub (a,b) | Mul (a,b) | Div (a,b) | Min (a,b) | Max (a,b) ->
      f (f acc a) b
  | Exp a | Erf a | Ceil a -> f acc a
  | Indicator c -> fold_condition f acc c
  | Cdf (_,ps,x) -> List.fold_left f acc (x :: ps)
  | Integral i ->
      let bounds = List.filter_map Fun.id [i.lower; i.upper] in
      List.fold_left f acc (i.body :: bounds @ i.parameters)
and fold_condition f acc = function
  | Compare (_,a,b) -> f (f acc a) b
  | Not c -> fold_condition f acc c
  | Bool_param _ -> acc

let rec mentions id = function
  | Var k -> k = id
  | e -> fold_children (fun found e -> found || mentions id e) false e

let rec parameters acc = function
  | Param p -> if List.mem p acc then acc else acc @ [p]
  | Indicator c -> condition_parameters acc c
  | e -> fold_children parameters acc e
and condition_parameters acc = function
  | Compare (_,a,b) -> parameters (parameters acc a) b
  | Not c -> condition_parameters acc c
  | Bool_param p -> if List.mem p acc then acc else acc @ [p]

let rec has_integral = function
  | Integral _ -> true
  | e -> fold_children (fun found e -> found || has_integral e) false e

let number x =
  let s = Printf.sprintf "%.15g" x in
  if float_of_string s = x then s else Printf.sprintf "%.17g" x

(* Precedence: 0 top level, 1 sums, 2 products, 3 atoms. *)
let rec show prec e =
  let paren p s = if p < prec then "(" ^ s ^ ")" else s in
  let call f args = f ^ "(" ^ String.concat ", " (List.map (show 0) args) ^ ")" in
  match e with
  | Const x -> if x < 0. then paren 1 (number x) else number x
  | Param p -> p
  | Var k -> Printf.sprintf "sample#%d" k
  | Add (a,b) -> paren 1 (show 1 a ^ " + " ^ show 2 b)
  | Sub (Const 0.,a) -> paren 1 ("-" ^ show 3 a)
  | Sub (a,b) -> paren 1 (show 1 a ^ " - " ^ show 2 b)
  | Mul (a,b) -> paren 2 (show 2 a ^ " * " ^ show 3 b)
  | Div (a,b) -> paren 2 (show 2 a ^ " / " ^ show 3 b)
  | Min (Max (e,lo),hi) -> call "clamp" [e;lo;hi]
  | Min (a,b) -> call "min" [a;b]
  | Max (a,b) -> call "max" [a;b]
  | Exp a -> call "exp" [a]
  | Erf a -> call "erf" [a]
  | Ceil a -> call "ceil" [a]
  | Indicator c -> "[" ^ show_condition c ^ "]"
  | Cdf (d,ps,x) -> "P(" ^ call (Distribution.name d) ps ^ " <= " ^ show 0 x ^ ")"
  | Integral i ->
      let x = Printf.sprintf "sample#%d" i.var in
      let range = match i.lower, i.upper with
        | None, None -> ""
        | Some lo, None -> ", " ^ x ^ " >= " ^ show 0 lo
        | None, Some hi -> ", " ^ x ^ " <= " ^ show 0 hi
        | Some lo, Some hi -> ", " ^ show 0 lo ^ " <= " ^ x ^ " <= " ^ show 0 hi
      in
      paren 2 ("∫[" ^ x ^ " ~ " ^ call (Distribution.name i.distribution) i.parameters
               ^ range ^ "] " ^ show 3 i.body)
and show_condition = function
  | Compare (op,a,b) -> show_compare op a b
  | Not (Compare (Lt,a,b)) -> show 1 a ^ " >= " ^ show 1 b
  | Not (Compare (Le,a,b)) -> show 1 a ^ " > " ^ show 1 b
  | Not (Compare (Eq,a,b)) -> show 1 a ^ " != " ^ show 1 b
  | Not c -> "not " ^ show_condition c
  | Bool_param p -> p
and show_compare op a b =
  show 1 a ^ (match op with Lt -> " < " | Le -> " <= " | Eq -> " = ") ^ show 1 b

let to_string = show 0
