(** Symbolic values and boundary records from Section Analysis of main.tex. *)
module Rational = struct
  type t = { num : int; den : int }
  exception Overflow
  let rec gcd a b = if b=0 then a else gcd b (a mod b)
  let checked n = if n=min_int then raise Overflow else n
  let mul_int a b =
    if a=0 || b=0 then 0 else
    if abs (checked a) > max_int / abs (checked b) then raise Overflow else a*b
  let add_int a b =
    let n=a+b in
    if (a>=0)=(b>=0) && (n>=0)<>(a>=0) then raise Overflow;
    checked n
  let make n d =
    if d=0 then raise Division_by_zero;
    let n=checked n and d=checked d in
    let g=gcd (abs n) (abs d) in
    let g=if d<0 then -g else g in
    {num=n/g;den=d/g}
  let of_int n = make n 1
  let zero=of_int 0 and one=of_int 1
  let neg n = {n with num= -(checked n.num)}
  let add a b =
    let g=gcd a.den b.den in
    make (add_int (mul_int a.num (b.den/g)) (mul_int b.num (a.den/g)))
      (mul_int a.den (b.den/g))
  let sub a b = add a (neg b)
  let mul a b =
    let g=gcd (abs a.num) b.den and h=gcd (abs b.num) a.den in
    make (mul_int (a.num/g) (b.num/h)) (mul_int (a.den/h) (b.den/g))
  let div a b = mul a (make b.den b.num)
  let compare a b = Stdlib.compare (sub a b).num 0
  let rec pow10 n = if n=0 then 1 else mul_int 10 (pow10 (n-1))
  let of_string text =
    let s=String.lowercase_ascii text in
    let mantissa,exponent=match String.index_opt s 'e' with
      | None -> s,0
      | Some i -> String.sub s 0 i,int_of_string (String.sub s (i+1) (String.length s-i-1)) in
    let digits,places=match String.index_opt mantissa '.' with
      | None -> mantissa,0
      | Some i -> String.sub mantissa 0 i ^ String.sub mantissa (i+1) (String.length mantissa-i-1),
                  String.length mantissa-i-1 in
    let n=int_of_string digits in
    let shift=exponent-places in
    if shift>18 || shift< -18 then raise Overflow;
    if shift>=0 then make (mul_int n (pow10 shift)) 1 else make n (pow10 (-shift))
  let to_string n =
    if n.den=1 then string_of_int n.num else Printf.sprintf "(%d/%d)" n.num n.den
end

type t =
  | Number of Rational.t | Boolean of bool | Parameter of string | Sample of int
  | Finite of int * int | Unit | Nil
  | Arith of Ast.arith * t * t
  | Compare of Ast.comparison * t * t
  | Finite_compare of Ast.comparison * int * t * t
  | And of t * t | Or of t * t | Not of t
  | Ite of t * t * t | Pair of t * t | Cons of t * t
  | Closure of { env : env; self : string option; param : string; body : Ast.expr }
and env = (string * t) list

type boundary = { path : t; guard : t; minus : t; plus : t }
type sample = { id : int; distribution : Ast.distribution }

let number s = Number (Rational.of_string s)
let integer n = Number (Rational.of_int n)
let zero=integer 0 and one=integer 1
let truth=Boolean true and falsity=Boolean false

let negate = function Boolean b -> Boolean (not b) | Not t -> t | t -> Not t
let and_ a b = match a,b with
  | Boolean false,_ | _,Boolean false -> falsity
  | Boolean true,x | x,Boolean true -> x
  | _ when a=b -> a
  | _ when a=negate b -> falsity
  | _ -> And (a,b)
let or_ a b = match a,b with
  | Boolean true,_ | _,Boolean true -> truth
  | Boolean false,x | x,Boolean false -> x
  | _ when a=b -> a
  | _ when a=negate b -> truth
  | _ -> Or (a,b)

let arith op a b =
  let raw () = Arith (op,a,b) in
  match a,b with
  | Number x,Number y ->
      (try Number ((match op with Ast.Add -> Rational.add | Sub -> Rational.sub
         | Mul -> Rational.mul | Div -> Rational.div) x y)
       with Rational.Overflow -> raw ())
  | _ -> match op with
    | Ast.Add when a=zero -> b | Add when b=zero -> a
    | Sub when b=zero -> a
    | Mul when a=one -> b | Mul when b=one -> a
    | Div when b=one -> a
    | _ -> raw ()

let comparison op a b =
  let raw () = Compare (op,a,b) in
  match a,b with
  | Number x,Number y ->
      (try let c=Rational.compare x y in Boolean (match op with Ast.Lt -> c<0 | Le -> c<=0 | Eq -> c=0)
       with Rational.Overflow -> raw ())
  | _ when a=b -> Boolean (op<>Ast.Lt)
  | _ -> raw ()

let finite_comparison op n a b = match a,b with
  | Finite (i,m),Finite (j,k) when m=n && k=n ->
      Boolean (match op with Ast.Lt -> i<j | Le -> i<=j | Eq -> i=j)
  | _ -> Finite_compare (op,n,a,b)

let arith_name = function Ast.Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
let compare_name = function Ast.Lt -> "<" | Le -> "<=" | Eq -> "="
let rec to_string = function
  | Number n -> Rational.to_string n | Boolean b -> string_of_bool b
  | Parameter name -> name | Sample id -> "s" ^ string_of_int id
  | Finite (i,n) -> Printf.sprintf "%d#%d" i n | Unit -> "()" | Nil -> "nil"
  | Arith (op,a,b) -> infix (arith_name op) a b
  | Compare (op,a,b) -> infix (compare_name op) a b
  | Finite_compare (op,n,a,b) -> infix (compare_name op ^ "#" ^ string_of_int n) a b
  | And (a,b) -> infix "and" a b | Or (a,b) -> infix "or" a b
  | Not t -> "not " ^ to_string t
  | Ite (c,a,b) -> Printf.sprintf "ite(%s, %s, %s)" (to_string c) (to_string a) (to_string b)
  | Pair (a,b) -> "(" ^ to_string a ^ ", " ^ to_string b ^ ")"
  | Cons (a,b) -> infix "::" a b
  | Closure c -> Printf.sprintf "closure([%s], %s%s, %s)"
      (String.concat "; " (List.map (fun (name,v) -> name ^ " -> " ^ to_string v) c.env))
      (match c.self with None -> "" | Some name -> name ^ ", ") c.param (Ast.to_string c.body)
and infix op a b = "(" ^ to_string a ^ " " ^ op ^ " " ^ to_string b ^ ")"

let union a b = List.fold_left (fun acc x -> if List.mem x acc then acc else acc @ [x]) a b

(** Rec(pi, phi, v1, v2): finite comparisons deliberately contribute no guard. *)
let rec record path condition minus plus = match condition with
  | Compare ((Ast.Lt | Le),a,b) -> [{path;guard=arith Ast.Sub a b;minus;plus}]
  | And (a,b) | Or (a,b) -> union (record path a minus plus) (record path b minus plus)
  | Not t -> record path t minus plus
  | Boolean _ | Finite_compare _ | Parameter _ -> []
  | _ -> invalid_arg "Condition is outside the paper's Boolean grammar"
