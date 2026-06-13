(* Type definitions for Slice *)

open Lat
open Lats

type cmp_op = Lt | Le

(* Generic expression structure *)
type 'a expr_generic =
  | Var    of string
  | Const  of float
  | BoolConst of bool
  | Let    of string * 'a * 'a
  | Sample of 'a sample
  | DiscreteCase of ('a * 'a) list      (* probability is now an expression *)
  | Cmp    of cmp_op * 'a * 'a * bool
  | And    of 'a * 'a
  | Or     of 'a * 'a
  | Not    of 'a
  | If     of 'a * 'a * 'a
  | Pair   of 'a * 'a
  | First  of 'a
  | Second of 'a
  | Fun    of string * 'a
  | FuncApp    of 'a * 'a
  | LoopApp    of 'a * 'a * int           (* Loop application: e1 e2 int *)
  | FinConst of int * int
  | FinCmp of cmp_op * 'a * 'a * int * bool
  | FinEq of 'a * 'a * int
  | Observe of 'a
  | Fix of string * string * 'a
  | Nil
  | Cons of 'a * 'a
  | MatchList of 'a * 'a * string * string * 'a
  | Ref of 'a
  | Deref of 'a
  | Assign of 'a * 'a
  | Seq of 'a * 'a
  | Unit
  | RuntimeError of string
  (* Arithmetic on (possibly symbolic) floats *)
  | Add of 'a * 'a
  | Sub of 'a * 'a
  | Mul of 'a * 'a
  | Div of 'a * 'a
  (* Internal generated special functions used by
     closed-form AD of CDF expressions (e.g. erf, exp, etc.). e.g. allows for stuff like: CDF(gaussian(0, 1), theta) --> 0.5 * (1 + erf(theta / sqrt(2))).
     These are not currently parsed from Slice syntax. *)
  | SpecialFunc of string * 'a list
  (* CDF of a continuous distribution evaluated at a point.
     Emitted only by the discretizer when symbolic cuts are present. *)
  | Cdf of 'a sample * 'a
  (* CDF of an arbitrary (sample-containing) expression evaluated at
     a point.  Used when the kernel on the LHS of a comparison is a
     compound expression like [uniform() + uniform()] rather than a
     bare [Sample]. *)
  | CdfExpr of 'a * 'a

and single_arg_dist_kind =
  | DExponential | DLaplace | DCauchy | DTDist | DChi2 | DLogistic | DRayleigh | DPoisson

and two_arg_dist_kind =
  | DUniform | DGaussian | DBeta | DLogNormal | DGamma | DPareto | DWeibull
  | DGumbel1 | DGumbel2 | DExppow | DBinomial

and 'a sample =
  | Distr1 of single_arg_dist_kind * 'a
  | Distr2 of two_arg_dist_kind * 'a * 'a


type expr = ExprNode of expr expr_generic

(* ================================================================ *)
(* Cut values, cut sets, and symbolic-expression sets               *)
(* These need to be declared after [expr] is defined because        *)
(* symbolic cuts and the sym-bag both carry [expr] payloads.        *)
(* ================================================================ *)

(* A cut value is either a concrete float constant or a symbolic
   expression (kept around verbatim so we can splice it into the
   discretized program). The string is the canonical identity used
   for equality / ordering: it is the pretty-printed form of the
   expression without ANSI color codes. *)
type cut_val =
  | CVConst of float
  | CVSym of string * expr

let compare_cut_val (a : cut_val) (b : cut_val) : int =
  match a, b with
  | CVConst f1, CVConst f2 -> compare f1 f2
  | CVConst _, CVSym _ -> -1
  | CVSym _, CVConst _ -> 1
  | CVSym (s1, _), CVSym (s2, _) -> compare s1 s2

(* A cut on a float-typed expression: < c or <= c, where c is a
   cut value (constant or symbolic). *)
type cut =
  | Less of cut_val   (* < c *)
  | LessEq of cut_val (* <= c *)

let compare_cut (b1 : cut) (b2 : cut) : int =
  match b1, b2 with
  | Less c1, Less c2 -> compare_cut_val c1 c2
  | LessEq c1, LessEq c2 -> compare_cut_val c1 c2
  | Less c1, LessEq c2 ->
      let cmp = compare_cut_val c1 c2 in
      if cmp = 0 then -1 else cmp
  | LessEq c1, Less c2 ->
      let cmp = compare_cut_val c1 c2 in
      if cmp = 0 then 1 else cmp

(* Only used for constant cuts -- determines which interval a
   concrete float lies in. *)
let satisfies_cut (f : float) (c : cut) : bool =
  match c with
  | Less (CVConst c)   -> f < c
  | LessEq (CVConst c) -> f <= c
  | Less (CVSym _) | LessEq (CVSym _) ->
      failwith "satisfies_cut: cannot evaluate a symbolic cut at a concrete float"

module CutOrder = struct
  type t = cut
  let compare = compare_cut
end
module CutSet = Set.Make(CutOrder)

module CutSetContents : Lat with type t = (cut, CutSet.t) set_or_top = struct
  type t = (cut, CutSet.t) set_or_top
  let union v1 v2 =
    match v1, v2 with
    | Top, _ -> Top
    | _, Top -> Top
    | Finite s1, Finite s2 -> Finite (CutSet.union s1 s2)
  let equal v1 v2 =
    match v1, v2 with
    | Top, Top -> true
    | Finite s1, Finite s2 -> CutSet.equal s1 s2
    | _, _ -> false
end

module OriginalCutLat = Make(CutSetContents)

module CutLat = struct
  include OriginalCutLat

  (* Add concrete floats as LessEq constant cuts to a cut bag.
     Used to record reachable constants of the left operand of a
     comparison as cuts on the cut bag. *)
  let add_all (float_s : FloatSet.t) (b_bag : bag) : unit =
    let current_content = get b_bag in
    match current_content with
    | Top -> ()
    | Finite current_cut_set ->
        let new_cuts_to_add =
          FloatSet.fold
            (fun f acc -> CutSet.add (LessEq (CVConst f)) acc)
            float_s
            CutSet.empty
        in
        let potentially_updated_cut_set =
          CutSet.union current_cut_set new_cuts_to_add
        in
        if not (CutSet.equal current_cut_set potentially_updated_cut_set) then
          let temp_bag_with_new_state =
            create (Finite potentially_updated_cut_set)
          in
          leq temp_bag_with_new_state b_bag
end

let fresh_cut_bag () : CutLat.bag =
  CutLat.create (Finite CutSet.empty)

(* ---------------- Symbolic-expression bag ---------------- *)
(* A SymSet element is a pair (canonical_string, original_expr).
   Equality and ordering use only the canonical string; the
   accompanying expr is the payload spliced back into the output. *)
module SymSet = Set.Make(struct
  type t = string * expr
  let compare (s1, _) (s2, _) = compare s1 s2
end)

module SymSetContents : Lat with type t = (string * expr, SymSet.t) set_or_top = struct
  type t = (string * expr, SymSet.t) set_or_top
  let union v1 v2 =
    match v1, v2 with
    | Top, _ -> Top
    | _, Top -> Top
    | Finite s1, Finite s2 -> Finite (SymSet.union s1 s2)
  let equal v1 v2 =
    match v1, v2 with
    | Top, Top -> true
    | Finite s1, Finite s2 -> SymSet.equal s1 s2
    | _, _ -> false
end

module SymLat = Make(SymSetContents)

let fresh_sym_bag () : SymLat.bag =
  SymLat.create (Finite SymSet.empty)

(* ================================================================ *)
(* Types                                                              *)
(* ================================================================ *)

type meta =
  | Unknown of (ty -> unit) list
  | Known of ty
and meta_ref = meta ref
and ty =
  | TBool
  | TFloat of CutLat.bag * FloatLat.bag * SymLat.bag
      (* cut bag (cuts applied to this expression),
         float bag (concrete constants this expression may take),
         sym bag (symbolic expressions this expression may take). *)
  | TPair of ty * ty
  | TFun of ty * ty
  | TFin of int
  | TMeta of meta_ref
  | TUnit
  | TList of ty
  | TRef of ty

(* Function to recursively dereference type variables *)
let rec force t =
  match t with
  | TMeta r ->
      (match !r with
      | Known t' -> force t' (* Recursively force the resolved type *)
      | Unknown _ -> t (* Return the TMeta itself if it's unresolved *))
  | _ -> t (* Return the type if it's not a TMeta *)

let listen (m : meta_ref) (f : ty -> unit) : unit =
  match !m with
  | Known t -> f t
  | Unknown fs -> m := Unknown (f :: fs)

let fresh_meta () : ty = TMeta (ref (Unknown []))

let assign (m : meta_ref) (t : ty) : unit =
  match !m with
  | Known _ -> failwith "Cannot assign to a known type"
  | Unknown fs -> m := Known t; List.iter (fun f -> f t) fs

(* Function to recursively set all bound bags in float types to top *)
let rec set_cut_bags_to_top (t : ty) : unit =
  match force t with
  | TFloat (cut_bag, _float_bag, _sym_bag) ->
      CutLat.leq (CutLat.create Top) cut_bag
  | TPair (t1, t2) ->
      set_cut_bags_to_top t1;
      set_cut_bags_to_top t2
  | TFun (t1, t2) ->
      set_cut_bags_to_top t1;
      set_cut_bags_to_top t2
  | TList t' ->
      set_cut_bags_to_top t'
  | TRef t' ->
      set_cut_bags_to_top t'
  | TMeta r ->
      listen r (fun resolved_t -> set_cut_bags_to_top resolved_t)
  | TBool | TFin _ | TUnit ->
      ()

type texpr = ty * aexpr
and aexpr = TAExprNode of texpr expr_generic

type value =
  | VBool of bool
  | VFloat of float
  | VPair of value * value
  | VFin of int * int (* value k, modulus n *)
  | VClosure of string * expr * env
  | VUnit
  | VNil
  | VCons of value * value
  | VRef of value ref
and env = (string * value) list

let rec string_of_value = function
  | VBool b -> string_of_bool b
  | VFloat f -> string_of_float f
  | VPair (v1, v2) -> Printf.sprintf "(%s, %s)" (string_of_value v1) (string_of_value v2)
  | VFin (k, n) -> Printf.sprintf "%d#%d" k n
  | VClosure (x, _, _) -> Printf.sprintf "<fun %s>" x
  | VUnit -> "()"
  | VNil -> "[]"
  | VCons (v_hd, VNil) -> Printf.sprintf "[%s]" (string_of_value v_hd)
  | VCons (v_hd, v_tl) -> Printf.sprintf "%s :: %s" (string_of_value v_hd) (string_of_value v_tl)
  | VRef v -> Printf.sprintf "ref(%s)" (string_of_value !v)
