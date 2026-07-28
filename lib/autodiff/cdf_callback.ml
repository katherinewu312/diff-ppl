exception Unsupported of string

let unsupported msg = raise (Unsupported msg)

let cdistr_pdf dist x =
  match dist with
  | Distributions.Uniform (lo, hi) ->
      if x = lo || x = hi then
        unsupported
          "the uniform CDF is not differentiable in its point at a support boundary"
      else Gsl.Randist.flat_pdf x ~a:lo ~b:hi
  | Distributions.Gaussian (mean, std) ->
      Gsl.Randist.gaussian_pdf (x -. mean) ~sigma:std
  | Distributions.Exponential rate ->
      Gsl.Randist.exponential_pdf x ~mu:(1.0 /. rate)
  | Distributions.Beta (alpha, beta) ->
      Gsl.Randist.beta_pdf x ~a:alpha ~b:beta
  | Distributions.LogNormal (mu, sigma) ->
      Gsl.Randist.lognormal_pdf x ~zeta:mu ~sigma
  | Distributions.Gamma (shape, scale) ->
      Gsl.Randist.gamma_pdf x ~a:shape ~b:scale
  | Distributions.Laplace scale ->
      Gsl.Randist.laplace_pdf x ~a:scale
  | Distributions.Cauchy scale ->
      Gsl.Randist.cauchy_pdf x ~a:scale
  | Distributions.Pareto (a, b) ->
      if x = b then
        unsupported
          "the Pareto CDF is not differentiable in its point at the support boundary"
      else Gsl.Randist.pareto_pdf x ~a ~b
  | Distributions.Weibull (a, b) ->
      Gsl.Randist.weibull_pdf x ~a ~b
  | Distributions.TDist nu ->
      Gsl.Randist.tdist_pdf x ~nu
  | Distributions.Chi2 nu ->
      Gsl.Randist.chisq_pdf x ~nu
  | Distributions.Logistic scale ->
      Gsl.Randist.logistic_pdf x ~a:scale
  | Distributions.Gumbel1 (a, b) ->
      Gsl.Randist.gumbel1_pdf x ~a ~b
  | Distributions.Gumbel2 (a, b) ->
      Gsl.Randist.gumbel2_pdf x ~a ~b
  | Distributions.Rayleigh sigma ->
      Gsl.Randist.rayleigh_pdf x ~sigma
  | Distributions.Exppow (a, b) ->
      Gsl.Randist.exppow_pdf x ~a ~b
  | Distributions.Poisson _ | Distributions.Binomial _ ->
      unsupported
        "Leibniz CDF callbacks require a continuous density; Poisson and Binomial have atoms"

let parameter_count = function
  | Distributions.Uniform _
  | Distributions.Gaussian _
  | Distributions.Beta _
  | Distributions.LogNormal _
  | Distributions.Gamma _
  | Distributions.Pareto _
  | Distributions.Weibull _
  | Distributions.Gumbel1 _
  | Distributions.Gumbel2 _
  | Distributions.Exppow _
  | Distributions.Binomial _ ->
      2
  | Distributions.Exponential _
  | Distributions.Laplace _
  | Distributions.Cauchy _
  | Distributions.TDist _
  | Distributions.Chi2 _
  | Distributions.Logistic _
  | Distributions.Rayleigh _
  | Distributions.Poisson _ ->
      1

let all_zero xs =
  List.for_all (( = ) 0.0) xs

let unsupported_direction label tangents =
  if all_zero tangents then 0.0
  else
    unsupported
      ("no exact CDF parameter derivative callback is implemented for " ^ label)

let scale_parameter_jvp dist scale point dscale =
  if dscale = 0.0 || point = neg_infinity || point = infinity then 0.0
  else (-.point /. scale) *. cdistr_pdf dist point *. dscale

let uniform_parameter_jvp lo hi point dlo dhi =
  if lo = hi then
    unsupported "the uniform CDF callback is not differentiable for a zero-width interval"
  else if point = lo && dlo <> 0.0 then
    unsupported
      "the uniform CDF is not differentiable in its lower endpoint at the support boundary"
  else if point = hi && dhi <> 0.0 then
    unsupported
      "the uniform CDF is not differentiable in its upper endpoint at the support boundary"
  else if point <= lo || point >= hi then 0.0
  else
    let width = hi -. lo in
    (((point -. hi) /. (width *. width)) *. dlo)
    -. (((point -. lo) /. (width *. width)) *. dhi)

let pareto_parameter_jvp a b point da db =
  if point = b && db <> 0.0 then
    unsupported
      "the Pareto CDF is not differentiable in its scale at the support boundary"
  else if point <= b then 0.0
  else
    let survival = (b /. point) ** a in
    (survival *. log (point /. b) *. da)
    -. ((a *. survival /. b) *. db)

let parameter_jvp dist direction point =
  if all_zero direction || point = neg_infinity || point = infinity then 0.0
  else
    match dist, direction with
    | Distributions.Uniform (lo, hi), [dlo; dhi] ->
        (* Leibniz with the moving support endpoints included explicitly. *)
        uniform_parameter_jvp lo hi point dlo dhi
    | Distributions.Pareto (a, b), [da; db] ->
        (* The scale [b] moves the support boundary, so its exact Leibniz
           boundary contribution is part of this closed-form rule. *)
        pareto_parameter_jvp a b point da db
    | Distributions.Gaussian (mean, std), [dmean; dstd] ->
        let pdf = cdistr_pdf dist point in
        (-.pdf *. dmean)
        -. (((point -. mean) /. std) *. pdf *. dstd)
    | Distributions.Exponential rate, [drate] ->
        if point <= 0.0 then 0.0
        else point *. exp (-.rate *. point) *. drate
    | Distributions.Beta _, [dalpha; dbeta] ->
        unsupported_direction "beta shape parameters" [dalpha; dbeta]
    | Distributions.LogNormal (mu, sigma), [dmu; dsigma] ->
        if point <= 0.0 then 0.0
        else
          let z = (log point -. mu) /. sigma in
          let phi =
            exp (-0.5 *. z *. z) /. sqrt (2.0 *. 4.0 *. atan 1.0)
          in
          (-.phi /. sigma *. dmu)
          -. (z *. phi /. sigma *. dsigma)
    | Distributions.Gamma (_, scale), [dshape; dscale] ->
        unsupported_direction "gamma shape" [dshape]
        +. scale_parameter_jvp dist scale point dscale
    | Distributions.Laplace scale, [dscale]
    | Distributions.Cauchy scale, [dscale]
    | Distributions.Logistic scale, [dscale]
    | Distributions.Rayleigh scale, [dscale] ->
        scale_parameter_jvp dist scale point dscale
    | Distributions.Weibull (scale, shape), [dscale; dshape] ->
        let scale_term = scale_parameter_jvp dist scale point dscale in
        if dshape = 0.0 || point <= 0.0 then scale_term
        else
          let ratio = point /. scale in
          let u = ratio ** shape in
          scale_term +. (exp (-.u) *. u *. log ratio *. dshape)
    | Distributions.TDist _, [dnu] ->
        unsupported_direction "Student-t degrees of freedom" [dnu]
    | Distributions.Chi2 _, [dnu] ->
        unsupported_direction "chi-square degrees of freedom" [dnu]
    | Distributions.Gumbel1 (a, b), [da; db] ->
        let exp_minus_ax = exp (-.a *. point) in
        let cdf = exp (-.b *. exp_minus_ax) in
        (cdf *. b *. point *. exp_minus_ax *. da)
        -. (cdf *. exp_minus_ax *. db)
    | Distributions.Gumbel2 (a, b), [da; db] ->
        if point <= 0.0 then 0.0
        else
          let x_minus_a = point ** (-.a) in
          let cdf = exp (-.b *. x_minus_a) in
          (cdf *. b *. x_minus_a *. log point *. da)
          -. (cdf *. x_minus_a *. db)
    | Distributions.Exppow (scale, _), [dscale; dshape] ->
        unsupported_direction "exponential-power shape" [dshape]
        +. scale_parameter_jvp dist scale point dscale
    | (Distributions.Poisson _ | Distributions.Binomial _), _ ->
        unsupported
          "exact continuous CDF derivative callbacks do not apply to Poisson or Binomial atoms"
    | _ -> invalid_arg "CDF tangent arity does not match distribution arity"

let jvp dist parameter_tangents point point_tangent =
  let moving_cut =
    if point_tangent = 0.0 || point = neg_infinity || point = infinity then 0.0
    else cdistr_pdf dist point *. point_tangent
  in
  moving_cut +. parameter_jvp dist parameter_tangents point

let basis size i =
  List.init size (fun j -> if i = j then 1.0 else 0.0)

let vjp dist parameter_active point point_active output_adjoint =
  let arity = parameter_count dist in
  if List.length parameter_active <> arity then
    invalid_arg "CDF VJP activity arity does not match distribution arity";
  if output_adjoint = 0.0 then List.init arity (fun _ -> 0.0), 0.0
  else
    let parameter_adjoints =
      List.init arity (fun i ->
        if List.nth parameter_active i then
          output_adjoint *. parameter_jvp dist (basis arity i) point
        else 0.0)
    in
    let point_adjoint =
      if not point_active || point = neg_infinity || point = infinity then 0.0
      else output_adjoint *. cdistr_pdf dist point
    in
    parameter_adjoints, point_adjoint

let dist_single kind arg =
  match Distributions.get_cdistr_from_single_arg_kind kind arg with
  | Ok dist -> dist
  | Error msg -> unsupported msg

let dist_two kind arg1 arg2 =
  match Distributions.get_cdistr_from_two_arg_kind kind arg1 arg2 with
  | Ok dist -> dist
  | Error msg -> unsupported msg

let jvp_single kind arg darg point dpoint =
  jvp (dist_single kind arg) [darg] point dpoint

let jvp_two kind arg1 arg2 darg1 darg2 point dpoint =
  jvp (dist_two kind arg1 arg2) [darg1; darg2] point dpoint

let vjp_single kind arg arg_active point point_active output_adjoint =
  match
    vjp (dist_single kind arg) [arg_active] point point_active output_adjoint
  with
  | [darg], dpoint -> darg, dpoint
  | _ -> invalid_arg "single-argument CDF VJP returned the wrong arity"

let vjp_two kind arg1 arg2 arg1_active arg2_active point point_active output_adjoint =
  match
    vjp (dist_two kind arg1 arg2) [arg1_active; arg2_active]
      point point_active output_adjoint
  with
  | [darg1; darg2], dpoint -> darg1, darg2, dpoint
  | _ -> invalid_arg "two-argument CDF VJP returned the wrong arity"
