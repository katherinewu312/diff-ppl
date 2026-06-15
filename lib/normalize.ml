(* Pre-pass that normalizes affine comparisons.

   Whenever a [Cmp] has the form [a*x + b op rhs] (where [x] is a
   sub-expression containing a [Sample] and [a], [b] are pure
   numeric constants), it is rewritten to

     x op' (rhs - b) / a

   with the operator flipped when [a < 0].  Only the LHS is
   normalized; the RHS is left untouched.

   Affine extraction recognizes Add/Sub/Mul/Div whose other operand
   is a pure numeric literal.  Anything else (e.g. symbolic
   variables, samples on both sides, or sample in a denominator)
   causes the rewrite to bail out and the original [Cmp] is kept. *)

open Ast

(* Recognize a sub-expression that evaluates to a numeric constant
   (literal or arithmetic over literals).  Returns [None] for
   anything that depends on a variable or a sample. *)
let rec try_eval_const (ExprNode e : expr) : float option =
  match e with
  | Const f -> Some f
  | Add (e1, e2) -> bin_const e1 e2 (+.)
  | Sub (e1, e2) -> bin_const e1 e2 (-.)
  | Mul (e1, e2) -> bin_const e1 e2 ( *. )
  | Div (e1, e2) ->
      (match try_eval_const e1, try_eval_const e2 with
       | Some _, Some 0.0 -> None
       | Some x, Some y -> Some (x /. y)
       | _ -> None)
  | SpecialFunc (name, args) ->
      let values = List.map try_eval_const args in
      if List.for_all Option.is_some values then
        Simplify.special_value name (List.map Option.get values)
      else None
  | _ -> None
and bin_const e1 e2 op =
  match try_eval_const e1, try_eval_const e2 with
  | Some x, Some y -> Some (op x y)
  | _ -> None

(* Set of variable names known to be bound to sample-containing
   expressions.  Used so that, e.g., [let x = uniform(0,1) in x + 5
   < theta] treats [x + 5] as sample-flavored just like
   [uniform(0,1) + 5] would be. *)
module StringSet = Set.Make(String)

(* Does the expression contain a [Sample] node anywhere, OR a
   reference to a variable that is known to hold a sample-flavored
   value?  The default empty environment ignores variable bindings,
   matching the previous behavior. *)
let rec contains_sample_env (env : StringSet.t) (ExprNode e : expr) : bool =
  match e with
  | Sample _ -> true
  | Var x -> StringSet.mem x env
  | Const _ | BoolConst _ | Nil | Unit
  | FinConst _ | RuntimeError _ -> false
  | Let (x, e1, e2) ->
      let e1_has = contains_sample_env env e1 in
      let env' = if e1_has then StringSet.add x env else env in
      e1_has || contains_sample_env env' e2
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2)
  | Cmp (_, e1, e2, _) | FinCmp (_, e1, e2, _, _) | FinEq (e1, e2, _)
  | And (e1, e2) | Or (e1, e2) | Pair (e1, e2) | FuncApp (e1, e2)
  | Cons (e1, e2) | Assign (e1, e2) | Seq (e1, e2) ->
      contains_sample_env env e1 || contains_sample_env env e2
  | Not e1 | First e1 | Second e1 | Observe e1
  | Ref e1 | Deref e1 -> contains_sample_env env e1
  | If (e1, e2, e3) ->
      contains_sample_env env e1 || contains_sample_env env e2 || contains_sample_env env e3
  | Fun (_, e1) | Fix (_, _, e1) -> contains_sample_env env e1
  | MatchList (e1, e2, _, _, e3) ->
      contains_sample_env env e1 || contains_sample_env env e2 || contains_sample_env env e3
  | DiscreteCase cases ->
      List.exists (fun (b, p) ->
        contains_sample_env env b || contains_sample_env env p) cases
  | Cdf (_, e1) -> contains_sample_env env e1
  | CdfExpr (k, e1) -> contains_sample_env env k || contains_sample_env env e1
  | SpecialFunc (_, args) ->
      List.exists (contains_sample_env env) args

let contains_sample (e : expr) : bool =
  contains_sample_env StringSet.empty e

(* Decompose [e] into [(scale, kernel, offset)] such that
   [e = scale * kernel + offset].  The kernel is an arbitrary
   sample-containing sub-expression (possibly itself a Mul/Add of
   multiple samples).  Constant factors and offsets are extracted
   recursively so that, e.g., [2 * u() * u() + 1] is decomposed
   as [(2.0, u()*u(), 1.0)] even though the parsed left-assoc
   form is [Mul(Mul(2, u), u)].

   Returns [None] when [e] contains no [Sample] (in which case it
   is a pure constant and we leave the comparison untouched). *)
let rec affine_of (env : StringSet.t) (e : expr) : (float * expr * float) option =
  if not (contains_sample_env env e) then None
  else
    let ExprNode node = e in
    match node with
    | Sample _ -> Some (1.0, e, 0.0)
    | Var _ -> Some (1.0, e, 0.0)
    | Add (e1, e2) -> affine_add env e1 e2
    | Sub (e1, e2) -> affine_sub env e1 e2
    | Mul (e1, e2) -> affine_mul env e1 e2
    | Div (e1, e2) ->
        (* Only constant divisor is supported. *)
        (match try_eval_const e2 with
         | Some k when k <> 0.0 ->
             (match affine_of env e1 with
              | Some (a, k1, b) -> Some (a /. k, k1, b /. k)
              | None -> None)
         | _ -> Some (1.0, e, 0.0))
    | _ ->
        (* Unknown shape -- treat as opaque kernel. *)
        Some (1.0, e, 0.0)

and affine_add env e1 e2 =
  match affine_of env e1, affine_of env e2 with
  | None, None -> None  (* impossible: e contains_sample *)
  | Some (a, k, b), None ->
      (* e2 is a pure const. *)
      (match try_eval_const e2 with
       | Some c -> Some (a, k, b +. c)
       | None -> Some (1.0, ExprNode (Add (recompose a k b, e2)), 0.0))
  | None, Some (a, k, b) ->
      (match try_eval_const e1 with
       | Some c -> Some (a, k, c +. b)
       | None -> Some (1.0, ExprNode (Add (e1, recompose a k b)), 0.0))
  | Some (a1, k1, b1), Some (a2, k2, b2) ->
      let new_kernel =
        ExprNode (Add (recompose_no_offset a1 k1, recompose_no_offset a2 k2))
      in
      Some (1.0, new_kernel, b1 +. b2)

and affine_sub env e1 e2 =
  match affine_of env e1, affine_of env e2 with
  | None, None -> None
  | Some (a, k, b), None ->
      (match try_eval_const e2 with
       | Some c -> Some (a, k, b -. c)
       | None -> Some (1.0, ExprNode (Sub (recompose a k b, e2)), 0.0))
  | None, Some (a, k, b) ->
      (match try_eval_const e1 with
       | Some c -> Some (-. a, k, c -. b)
       | None -> Some (1.0, ExprNode (Sub (e1, recompose a k b)), 0.0))
  | Some (a1, k1, b1), Some (a2, k2, b2) ->
      let new_kernel =
        ExprNode (Sub (recompose_no_offset a1 k1, recompose_no_offset a2 k2))
      in
      Some (1.0, new_kernel, b1 -. b2)

and affine_mul env e1 e2 =
  match affine_of env e1, affine_of env e2 with
  | None, None -> None
  | Some (a, k, b), None ->
      (match try_eval_const e2 with
       | Some c -> Some (a *. c, k, b *. c)
       | None ->
           Some (1.0, ExprNode (Mul (recompose a k b, e2)), 0.0))
  | None, Some (a, k, b) ->
      (match try_eval_const e1 with
       | Some c -> Some (c *. a, k, c *. b)
       | None ->
           Some (1.0, ExprNode (Mul (e1, recompose a k b)), 0.0))
  | Some (a1, k1, b1), Some (a2, k2, b2) ->
      if b1 = 0.0 && b2 = 0.0 then
        Some (a1 *. a2, ExprNode (Mul (k1, k2)), 0.0)
      else
        let new_kernel =
          ExprNode (Mul (recompose a1 k1 b1, recompose a2 k2 b2))
        in
        Some (1.0, new_kernel, 0.0)

(* Rebuild an expression [a*k + b] using minimal-noise output. *)
and recompose (a : float) (k : expr) (b : float) : expr =
  let ak = recompose_no_offset a k in
  if b = 0.0 then ak
  else if b > 0.0 then ExprNode (Add (ak, ExprNode (Const b)))
  else ExprNode (Sub (ak, ExprNode (Const (-. b))))

and recompose_no_offset (a : float) (k : expr) : expr =
  if a = 1.0 then k
  else if a = -1.0 then ExprNode (Sub (ExprNode (Const 0.0), k))
  else ExprNode (Mul (ExprNode (Const a), k))

(* Rewrite [Cmp (op, lhs, rhs, flipped)] when [lhs] is affine in a
   sample.  Returns the new comparison expression. *)
let normalize_cmp (env : StringSet.t) (op : cmp_op) (lhs : expr) (rhs : expr) (flipped : bool) : expr =
  match affine_of env lhs with
  | None -> ExprNode (Cmp (op, lhs, rhs, flipped))
  | Some (a, x, b) when a = 1.0 && b = 0.0 ->
      ExprNode (Cmp (op, x, rhs, flipped))
  | Some (a, x, b) ->
      let new_rhs =
        match try_eval_const rhs with
        | Some r -> ExprNode (Const ((r -. b) /. a))
        | None ->
            let rhs_minus_b =
              if b = 0.0 then rhs
              else if b < 0.0 then
                ExprNode (Add (rhs, ExprNode (Const (-. b))))
              else
                ExprNode (Sub (rhs, ExprNode (Const b)))
            in
            if a = 1.0 then rhs_minus_b
            else if a = -1.0 then
              ExprNode (Sub (ExprNode (Const 0.0), rhs_minus_b))
            else
              ExprNode (Div (rhs_minus_b, ExprNode (Const a)))
      in
      if a > 0.0 then
        ExprNode (Cmp (op, x, new_rhs, flipped))
      else
        ExprNode (Cmp (op, new_rhs, x, not flipped))

(* Recursive rewriter that threads a [StringSet] of variable names
   known to be bound to sample-flavored expressions.  Crossing a
   [Let x = e1] grows the environment with [x] iff [e1] is
   sample-flavored. *)
let rec normalize_env (env : StringSet.t) (e : expr) : expr =
  let ExprNode node = e in
  match node with
  | Cmp (op, e1, e2, flipped) ->
      let e1' = normalize_env env e1 in
      let e2' = normalize_env env e2 in
      normalize_cmp env op e1' e2' flipped
  | Const _ | Var _ | BoolConst _ | Nil | Unit
  | FinConst _ | RuntimeError _ -> e
  | Let (x, e1, e2) ->
      let e1' = normalize_env env e1 in
      let env' =
        if contains_sample_env env e1' then StringSet.add x env else env
      in
      ExprNode (Let (x, e1', normalize_env env' e2))
  | Sample (Distr1 (k, e1)) -> ExprNode (Sample (Distr1 (k, normalize_env env e1)))
  | Sample (Distr2 (k, e1, e2)) -> ExprNode (Sample (Distr2 (k, normalize_env env e1, normalize_env env e2)))
  | DiscreteCase cases ->
      ExprNode (DiscreteCase (List.map (fun (b, p) -> (normalize_env env b, normalize_env env p)) cases))
  | FinCmp (op, e1, e2, n, flipped) ->
      ExprNode (FinCmp (op, normalize_env env e1, normalize_env env e2, n, flipped))
  | FinEq (e1, e2, n) -> ExprNode (FinEq (normalize_env env e1, normalize_env env e2, n))
  | And (e1, e2) -> ExprNode (And (normalize_env env e1, normalize_env env e2))
  | Or (e1, e2) -> ExprNode (Or (normalize_env env e1, normalize_env env e2))
  | Not e1 -> ExprNode (Not (normalize_env env e1))
  | If (e1, e2, e3) -> ExprNode (If (normalize_env env e1, normalize_env env e2, normalize_env env e3))
  | Pair (e1, e2) -> ExprNode (Pair (normalize_env env e1, normalize_env env e2))
  | First e1 -> ExprNode (First (normalize_env env e1))
  | Second e1 -> ExprNode (Second (normalize_env env e1))
  | Fun (x, e1) ->
      (* Inside a [fun] we don't know whether the parameter will be
         bound to a sample-flavored value, so drop it from the env
         to be safe. *)
      let env' = StringSet.remove x env in
      ExprNode (Fun (x, normalize_env env' e1))
  | FuncApp (e1, e2) -> ExprNode (FuncApp (normalize_env env e1, normalize_env env e2))
  | Observe e1 -> ExprNode (Observe (normalize_env env e1))
  | Fix (f, x, e1) ->
      let env' = StringSet.remove f (StringSet.remove x env) in
      ExprNode (Fix (f, x, normalize_env env' e1))
  | Cons (e1, e2) -> ExprNode (Cons (normalize_env env e1, normalize_env env e2))
  | MatchList (e1, en, y, ys, ec) ->
      let env' = StringSet.remove y (StringSet.remove ys env) in
      ExprNode (MatchList (normalize_env env e1, normalize_env env en, y, ys, normalize_env env' ec))
  | Ref e1 -> ExprNode (Ref (normalize_env env e1))
  | Deref e1 -> ExprNode (Deref (normalize_env env e1))
  | Assign (e1, e2) -> ExprNode (Assign (normalize_env env e1, normalize_env env e2))
  | Seq (e1, e2) -> ExprNode (Seq (normalize_env env e1, normalize_env env e2))
  | Add (e1, e2) -> ExprNode (Add (normalize_env env e1, normalize_env env e2))
  | Sub (e1, e2) -> ExprNode (Sub (normalize_env env e1, normalize_env env e2))
  | Mul (e1, e2) -> ExprNode (Mul (normalize_env env e1, normalize_env env e2))
  | Div (e1, e2) -> ExprNode (Div (normalize_env env e1, normalize_env env e2))
  | SpecialFunc (name, args) ->
      ExprNode (SpecialFunc (name, List.map (normalize_env env) args))
  | Cdf (Distr1 (k, e1), e2) -> ExprNode (Cdf (Distr1 (k, normalize_env env e1), normalize_env env e2))
  | Cdf (Distr2 (k, e1, e2), e3) -> ExprNode (Cdf (Distr2 (k, normalize_env env e1, normalize_env env e2), normalize_env env e3))
  | CdfExpr (k, e1) -> ExprNode (CdfExpr (normalize_env env k, normalize_env env e1))

let normalize (e : expr) : expr =
  normalize_env StringSet.empty e
