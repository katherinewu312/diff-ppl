open Ast

let node e = ExprNode e
let runtime_error msg = node (RuntimeError ("ADEV: " ^ msg))

let const = Simplify.mk_const
let add = Simplify.mk_add
let sub = Simplify.mk_sub
let mul = Simplify.mk_mul
let div = Simplify.mk_div

let zero = const 0.0
let one = const 1.0
let two = const 2.0
let half = const 0.5
let pi = const (4.0 *. atan 1.0)
let sqrt_two = const (sqrt 2.0)
let sqrt_two_pi = const (sqrt (2.0 *. 4.0 *. atan 1.0))

let special name args =
  Simplify.mk_special name args

let exp_ x = special "exp" [x]
let log_ x = special "log" [x]
let pow_ x y = special "pow" [x; y]
let erf_ x = special "erf" [x]
let atan_ x = special "atan" [x]
let abs_ x = special "abs" [x]
let beta_ a b = special "beta" [a; b]
let gamma_ a = special "gamma" [a]
let beta_inc a b x = special "beta_inc" [a; b; x]
let gamma_inc_p a x = special "gamma_inc_P" [a; x]

let neg x = sub zero x
let square x = mul x x

let dual_primal e =
  match Simplify.expr e with
  | ExprNode (Pair (p, _)) -> p
  | e' -> Simplify.mk_first e'

let dual_tangent e =
  match Simplify.expr e with
  | ExprNode (Pair (_, t)) -> t
  | e' -> Simplify.mk_second e'

type dual =
  { primal : expr
  ; tangent : expr
  }

let dual e = { primal = dual_primal e; tangent = dual_tangent e }

let dual_pair primal tangent =
  Simplify.expr (Simplify.mk_pair primal tangent)

let unsupported_tangent primal msg =
  dual_pair primal (runtime_error msg)

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

let is_zero_expr e =
  match Simplify.expr e with
  | ExprNode (Const f) -> f = 0.0
  | _ -> false

let require_zero_tangents primal label tangents build =
  if List.for_all (fun e -> is_zero_expr e) tangents then build ()
  else
    unsupported_tangent primal
      ("CDF derivative for " ^ label
       ^ " currently supports differentiation through the CDF point only")

let d_sub a b =
  { primal = sub a.primal b.primal
  ; tangent = sub a.tangent b.tangent
  }

let d_mul a b =
  { primal = mul a.primal b.primal
  ; tangent = add (mul a.primal b.tangent) (mul a.tangent b.primal)
  }

let d_div a b =
  { primal = div a.primal b.primal
  ; tangent =
      div
        (sub (mul a.tangent b.primal) (mul a.primal b.tangent))
        (square b.primal)
  }

let d_log a =
  { primal = log_ a.primal
  ; tangent = div a.tangent a.primal
  }

let d_pow a b =
  let primal = pow_ a.primal b.primal in
  { primal
  ; tangent =
      mul primal
        (add
           (mul b.tangent (log_ a.primal))
           (mul b.primal (div a.tangent a.primal)))
  }

let normal_cdf z =
  mul half (add one (erf_ (div z sqrt_two)))

let normal_pdf z =
  div (exp_ (mul (const (-0.5)) (square z))) sqrt_two_pi

let gamma_pdf shape z =
  div
    (mul (pow_ z (sub shape one)) (exp_ (neg z)))
    (gamma_ shape)

let beta_pdf alpha beta x =
  div
    (mul
       (pow_ x (sub alpha one))
       (pow_ (sub one x) (sub beta one)))
    (beta_ alpha beta)

let uniform_cdf lo hi point =
  (* Interior-support rule, exact when lo < x < hi. *)
  let lo = dual lo in
  let hi = dual hi in
  let x = dual point in
  let width = d_sub hi lo in
  let x_minus_lo = d_sub x lo in
  let result = d_div x_minus_lo width in
  dual_pair result.primal result.tangent

let gaussian_cdf mean std point =
  let mean = dual mean in
  let std = dual std in
  let x = dual point in
  let z = d_div (d_sub x mean) std in
  dual_pair (normal_cdf z.primal) (mul (normal_pdf z.primal) z.tangent)

let lognormal_cdf mu sigma point =
  let mu = dual mu in
  let sigma = dual sigma in
  let x = dual point in
  let z = d_div (d_sub (d_log x) mu) sigma in
  dual_pair (normal_cdf z.primal) (mul (normal_pdf z.primal) z.tangent)

let exponential_cdf rate point =
  let rate = dual rate in
  let x = dual point in
  let u = d_mul rate x in
  let exp_neg_u = exp_ (neg u.primal) in
  dual_pair (sub one exp_neg_u) (mul exp_neg_u u.tangent)

let logistic_cdf scale point =
  let scale = dual scale in
  let x = dual point in
  let z = d_div x scale in
  let primal = div one (add one (exp_ (neg z.primal))) in
  let tangent = mul (mul primal (sub one primal)) z.tangent in
  dual_pair primal tangent

let cauchy_cdf scale point =
  let scale = dual scale in
  let x = dual point in
  let z = d_div x scale in
  let primal = add half (div (atan_ z.primal) pi) in
  let tangent = div z.tangent (mul pi (add one (square z.primal))) in
  dual_pair primal tangent

let rayleigh_cdf sigma point =
  let sigma = dual sigma in
  let x = dual point in
  let u = d_div { primal = square x.primal; tangent = mul two (mul x.primal x.tangent) }
      { primal = mul two (square sigma.primal)
      ; tangent = mul (const 4.0) (mul sigma.primal sigma.tangent)
      }
  in
  let exp_neg_u = exp_ (neg u.primal) in
  dual_pair (sub one exp_neg_u) (mul exp_neg_u u.tangent)

let weibull_cdf scale shape point =
  let scale = dual scale in
  let shape = dual shape in
  let x = dual point in
  let base = d_div x scale in
  let u = d_pow base shape in
  let exp_neg_u = exp_ (neg u.primal) in
  dual_pair (sub one exp_neg_u) (mul exp_neg_u u.tangent)

let beta_cdf alpha beta point =
  let alpha = dual alpha in
  let beta = dual beta in
  let x = dual point in
  let primal = beta_inc alpha.primal beta.primal x.primal in
  require_zero_tangents primal "beta" [alpha.tangent; beta.tangent] (fun () ->
    dual_pair primal (mul (beta_pdf alpha.primal beta.primal x.primal) x.tangent))

let gamma_cdf shape scale point =
  let shape = dual shape in
  let scale = dual scale in
  let x = dual point in
  let z = d_div x scale in
  let primal = gamma_inc_p shape.primal z.primal in
  require_zero_tangents primal "gamma shape parameter" [shape.tangent] (fun () ->
    dual_pair primal (mul (gamma_pdf shape.primal z.primal) z.tangent))

let chi2_cdf nu point =
  let nu = dual nu in
  let x = dual point in
  let shape = div nu.primal two in
  let z = { primal = div x.primal two; tangent = div x.tangent two } in
  let primal = gamma_inc_p shape z.primal in
  require_zero_tangents primal "chi2 degrees-of-freedom parameter" [nu.tangent] (fun () ->
    dual_pair primal (mul (gamma_pdf shape z.primal) z.tangent))

let laplace_cdf scale point =
  let scale = dual scale in
  let x = dual point in
  let z = d_div x scale in
  let primal =
    node
      (If
         ( node (Cmp (Lt, x.primal, zero, false))
         , mul half (exp_ z.primal)
         , sub one (mul half (exp_ (neg z.primal))) ))
  in
  require_zero_tangents primal "laplace scale parameter" [scale.tangent] (fun () ->
    let pdf = div (exp_ (neg (abs_ z.primal))) (mul two scale.primal) in
    dual_pair primal (mul pdf x.tangent))

type single_arg_rule =
  { single_kind : single_arg_dist_kind
  ; single_name : string
  ; single_cdf : expr -> expr -> expr
  }

type two_arg_rule =
  { two_kind : two_arg_dist_kind
  ; two_name : string
  ; two_cdf : expr -> expr -> expr -> expr
  }

let single_arg_rules =
  [ { single_kind = DExponential; single_name = "exponential"; single_cdf = exponential_cdf }
  ; { single_kind = DLaplace; single_name = "laplace"; single_cdf = laplace_cdf }
  ; { single_kind = DCauchy; single_name = "cauchy"; single_cdf = cauchy_cdf }
  ; { single_kind = DChi2; single_name = "chi2"; single_cdf = chi2_cdf }
  ; { single_kind = DLogistic; single_name = "logistic"; single_cdf = logistic_cdf }
  ; { single_kind = DRayleigh; single_name = "rayleigh"; single_cdf = rayleigh_cdf }
  ]

let two_arg_rules =
  [ { two_kind = DUniform; two_name = "uniform"; two_cdf = uniform_cdf }
  ; { two_kind = DGaussian; two_name = "gaussian"; two_cdf = gaussian_cdf }
  ; { two_kind = DBeta; two_name = "beta"; two_cdf = beta_cdf }
  ; { two_kind = DLogNormal; two_name = "lognormal"; two_cdf = lognormal_cdf }
  ; { two_kind = DGamma; two_name = "gamma"; two_cdf = gamma_cdf }
  ; { two_kind = DWeibull; two_name = "weibull"; two_cdf = weibull_cdf }
  ]

let find_single_rule kind =
  List.find_opt (fun rule -> rule.single_kind = kind) single_arg_rules

let find_two_rule kind =
  List.find_opt (fun rule -> rule.two_kind = kind) two_arg_rules

let cdf dist point =
  match dist with
  | Distr1 (kind, arg) ->
      (match find_single_rule kind with
       | Some rule -> rule.single_cdf arg point
       | None -> unsupported_cdf dist point)
  | Distr2 (kind, arg1, arg2) ->
      (match find_two_rule kind with
       | Some rule -> rule.two_cdf arg1 arg2 point
       | None -> unsupported_cdf dist point)

let cdf_expr kernel point =
  unsupported_cdf_expr kernel point
