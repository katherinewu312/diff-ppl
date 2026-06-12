open Ast

let node e = ExprNode e
let runtime_error msg = node (RuntimeError ("ADEV: " ^ msg))

let dual_primal e =
  match Simplify.expr e with
  | ExprNode (Pair (p, _)) -> p
  | e' -> Simplify.mk_first e'

let dual_tangent e =
  match Simplify.expr e with
  | ExprNode (Pair (_, t)) -> t
  | e' -> Simplify.mk_second e'

let dual_pair primal tangent =
  Simplify.expr (Simplify.mk_pair primal tangent)

let sample_primal = function
  | Distr1 (kind, e1) -> Distr1 (kind, dual_primal e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, dual_primal e1, dual_primal e2)

let unsupported_cdf dist point =
  dual_pair
    (node (Cdf (sample_primal dist, dual_primal point)))
    (runtime_error "differentiation of this CDF expression is not implemented")

let unsupported_cdf_expr kernel point =
  dual_pair
    (node (CdfExpr (dual_primal kernel, dual_primal point)))
    (runtime_error "differentiation of CDF expressions over compound kernels is not implemented")

let uniform_cdf lo hi point =
  (* Interior-support rule:

       CDF(uniform(lo, hi), x) = (x - lo) / (hi - lo)

     The derivative follows by ordinary dual-number arithmetic. This
     is exact for lo < x < hi. Boundary/outside-support piecewise
     behavior can be added here later when the language has a compact
     representation for that piecewise derivative. *)
  let lo_p = dual_primal lo in
  let lo_t = dual_tangent lo in
  let hi_p = dual_primal hi in
  let hi_t = dual_tangent hi in
  let x_p = dual_primal point in
  let x_t = dual_tangent point in
  let width = Simplify.mk_sub hi_p lo_p in
  let x_minus_lo = Simplify.mk_sub x_p lo_p in
  let width_t = Simplify.mk_sub hi_t lo_t in
  let x_minus_lo_t = Simplify.mk_sub x_t lo_t in
  let primal = Simplify.mk_div x_minus_lo width in
  let tangent =
    Simplify.mk_div
      (Simplify.mk_sub
         (Simplify.mk_mul x_minus_lo_t width)
         (Simplify.mk_mul x_minus_lo width_t))
      (Simplify.mk_mul width width)
  in
  dual_pair primal tangent

let cdf dist point =
  match dist with
  | Distr2 (DUniform, lo, hi) -> uniform_cdf lo hi point
  | _ -> unsupported_cdf dist point

let cdf_expr kernel point =
  unsupported_cdf_expr kernel point
