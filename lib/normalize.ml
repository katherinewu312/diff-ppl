(* Pre-pass that normalises affine comparisons.

   Whenever a [Cmp] has the form [a*x + b op rhs] (where [x] is a
   sub-expression containing a [Sample] and [a], [b] are pure
   numeric constants), it is rewritten to

     x op' (rhs - b) / a

   with the operator flipped when [a < 0].  Only the LHS is
   normalised; the RHS is left untouched.

   Affine extraction recognises Add/Sub/Mul/Div whose other operand
   is a pure numeric literal.  Anything else (e.g. symbolic
   variables, samples on both sides, or sample in a denominator)
   causes the rewrite to bail out and the original [Cmp] is kept. *)

open Ast

(* Recognise a sub-expression that evaluates to a numeric constant
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
  | _ -> None
and bin_const e1 e2 op =
  match try_eval_const e1, try_eval_const e2 with
  | Some x, Some y -> Some (op x y)
  | _ -> None

(* Does the expression contain a [Sample] node anywhere? *)
let rec contains_sample (ExprNode e : expr) : bool =
  match e with
  | Sample _ -> true
  | Const _ | Var _ | BoolConst _ | Nil | Unit
  | FinConst _ | RuntimeError _ -> false
  | Let (_, e1, e2) -> contains_sample e1 || contains_sample e2
  | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2) | Div (e1, e2)
  | Cmp (_, e1, e2, _) | FinCmp (_, e1, e2, _, _) | FinEq (e1, e2, _)
  | And (e1, e2) | Or (e1, e2) | Pair (e1, e2) | FuncApp (e1, e2)
  | LoopApp (e1, e2, _) | Cons (e1, e2) | Assign (e1, e2) | Seq (e1, e2) ->
      contains_sample e1 || contains_sample e2
  | Not e1 | First e1 | Second e1 | Observe e1
  | Ref e1 | Deref e1 -> contains_sample e1
  | If (e1, e2, e3) ->
      contains_sample e1 || contains_sample e2 || contains_sample e3
  | Fun (_, e1) | Fix (_, _, e1) -> contains_sample e1
  | MatchList (e1, e2, _, _, e3) ->
      contains_sample e1 || contains_sample e2 || contains_sample e3
  | DistrCase cases ->
      List.exists (fun (b, p) -> contains_sample b || contains_sample p) cases
  | Cdf (_, e1) -> contains_sample e1

(* Try to decompose an expression into an affine form [a*x + b]
   where [x] is the (unique) sub-expression containing a [Sample]
   and [a], [b] are concrete floats.  Returns [None] when the
   expression is not affine in a single sample sub-expression. *)
let rec affine_of (e : expr) : (float * expr * float) option =
  let ExprNode node = e in
  (* If the expression itself is a constant, it is not affine in
     any sample. *)
  if not (contains_sample e) then None
  else
    match node with
    | Sample _ -> Some (1.0, e, 0.0)
    | Add (e1, e2) ->
        (match try_eval_const e2 with
         | Some k ->
             (match affine_of e1 with
              | Some (a, x, b) -> Some (a, x, b +. k)
              | None -> None)
         | None ->
             match try_eval_const e1 with
             | Some k ->
                 (match affine_of e2 with
                  | Some (a, x, b) -> Some (a, x, k +. b)
                  | None -> None)
             | None -> None)
    | Sub (e1, e2) ->
        (match try_eval_const e2 with
         | Some k ->
             (match affine_of e1 with
              | Some (a, x, b) -> Some (a, x, b -. k)
              | None -> None)
         | None ->
             match try_eval_const e1 with
             | Some k ->
                 (match affine_of e2 with
                  | Some (a, x, b) -> Some (-. a, x, k -. b)
                  | None -> None)
             | None -> None)
    | Mul (e1, e2) ->
        (match try_eval_const e2 with
         | Some k ->
             (match affine_of e1 with
              | Some (a, x, b) -> Some (a *. k, x, b *. k)
              | None -> None)
         | None ->
             match try_eval_const e1 with
             | Some k ->
                 (match affine_of e2 with
                  | Some (a, x, b) -> Some (k *. a, x, k *. b)
                  | None -> None)
             | None -> None)
    | Div (e1, e2) ->
        (* Only support sample / const, never const / sample. *)
        (match try_eval_const e2 with
         | Some k when k <> 0.0 ->
             (match affine_of e1 with
              | Some (a, x, b) -> Some (a /. k, x, b /. k)
              | None -> None)
         | _ -> None)
    | _ -> None

(* Rewrite [Cmp (op, lhs, rhs, flipped)] when [lhs] is affine in a
   sample.  Returns the new comparison expression. *)
let normalise_cmp (op : cmp_op) (lhs : expr) (rhs : expr) (flipped : bool) : expr =
  match affine_of lhs with
  | None -> ExprNode (Cmp (op, lhs, rhs, flipped))
  | Some (a, x, b) when a = 1.0 && b = 0.0 ->
      ExprNode (Cmp (op, x, rhs, flipped))
  | Some (a, x, b) ->
      (* new_rhs = (rhs - b) / a
         If [rhs] is itself a numeric constant, fold the whole new
         RHS to a single [Const].  Otherwise prefer the prettier
         forms: subtract a negative constant as an addition;
         divide by -1 as negate. *)
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

(* Recursive rewriter applied to every sub-expression. *)
let rec normalise (e : expr) : expr =
  let ExprNode node = e in
  match node with
  | Cmp (op, e1, e2, flipped) ->
      let e1' = normalise e1 in
      let e2' = normalise e2 in
      normalise_cmp op e1' e2' flipped
  | Const _ | Var _ | BoolConst _ | Nil | Unit
  | FinConst _ | RuntimeError _ -> e
  | Let (x, e1, e2) -> ExprNode (Let (x, normalise e1, normalise e2))
  | Sample (Distr1 (k, e1)) -> ExprNode (Sample (Distr1 (k, normalise e1)))
  | Sample (Distr2 (k, e1, e2)) -> ExprNode (Sample (Distr2 (k, normalise e1, normalise e2)))
  | DistrCase cases ->
      ExprNode (DistrCase (List.map (fun (b, p) -> (normalise b, normalise p)) cases))
  | FinCmp (op, e1, e2, n, flipped) ->
      ExprNode (FinCmp (op, normalise e1, normalise e2, n, flipped))
  | FinEq (e1, e2, n) -> ExprNode (FinEq (normalise e1, normalise e2, n))
  | And (e1, e2) -> ExprNode (And (normalise e1, normalise e2))
  | Or (e1, e2) -> ExprNode (Or (normalise e1, normalise e2))
  | Not e1 -> ExprNode (Not (normalise e1))
  | If (e1, e2, e3) -> ExprNode (If (normalise e1, normalise e2, normalise e3))
  | Pair (e1, e2) -> ExprNode (Pair (normalise e1, normalise e2))
  | First e1 -> ExprNode (First (normalise e1))
  | Second e1 -> ExprNode (Second (normalise e1))
  | Fun (x, e1) -> ExprNode (Fun (x, normalise e1))
  | FuncApp (e1, e2) -> ExprNode (FuncApp (normalise e1, normalise e2))
  | LoopApp (e1, e2, n) -> ExprNode (LoopApp (normalise e1, normalise e2, n))
  | Observe e1 -> ExprNode (Observe (normalise e1))
  | Fix (f, x, e1) -> ExprNode (Fix (f, x, normalise e1))
  | Cons (e1, e2) -> ExprNode (Cons (normalise e1, normalise e2))
  | MatchList (e1, en, y, ys, ec) ->
      ExprNode (MatchList (normalise e1, normalise en, y, ys, normalise ec))
  | Ref e1 -> ExprNode (Ref (normalise e1))
  | Deref e1 -> ExprNode (Deref (normalise e1))
  | Assign (e1, e2) -> ExprNode (Assign (normalise e1, normalise e2))
  | Seq (e1, e2) -> ExprNode (Seq (normalise e1, normalise e2))
  | Add (e1, e2) -> ExprNode (Add (normalise e1, normalise e2))
  | Sub (e1, e2) -> ExprNode (Sub (normalise e1, normalise e2))
  | Mul (e1, e2) -> ExprNode (Mul (normalise e1, normalise e2))
  | Div (e1, e2) -> ExprNode (Div (normalise e1, normalise e2))
  | Cdf (Distr1 (k, e1), e2) -> ExprNode (Cdf (Distr1 (k, normalise e1), normalise e2))
  | Cdf (Distr2 (k, e1, e2), e3) -> ExprNode (Cdf (Distr2 (k, normalise e1, normalise e2), normalise e3))
