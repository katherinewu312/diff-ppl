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
let sqrt_ x = special "sqrt" [x]
let erf_ x = special "erf" [x]
let atan_ x = special "atan" [x]
let abs_ x = special "abs" [x]
let beta_ a b = special "beta" [a; b]
let gamma_ a = special "gamma" [a]
let beta_inc a b x = special "beta_inc" [a; b; x]
let gamma_inc_p a x = special "gamma_inc_P" [a; x]

let neg x = sub zero x
let square x = mul x x

let rec factorial n =
  if n <= 1 then 1.0 else float_of_int n *. factorial (n - 1)

let if_ cond then_ else_ =
  node (If (cond, then_, else_))

let lt a b =
  node (Cmp (Lt, a, b, false))

let pow_int x n =
  match n with
  | 0 -> one
  | 1 -> x
  | _ -> pow_ x (const (float_of_int n))

let positive_pow x n =
  if_ (lt x zero) zero (pow_int x n)

let product_exprs = function
  | [] -> one
  | x :: xs -> List.fold_left mul x xs

let sum_exprs = function
  | [] -> zero
  | x :: xs -> List.fold_left add x xs

let signed_sum_exprs terms =
  List.fold_left
    (fun acc (sign, e) -> if sign >= 0 then add acc e else sub acc e)
    zero
    terms

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

let deterministic_dual e =
  match Simplify.expr e with
  | ExprNode (Pair _) -> dual e
  | e' -> { primal = e'; tangent = zero }

let dual_pair primal tangent =
  Simplify.expr (Simplify.mk_pair primal tangent)

let dual_expr d =
  dual_pair d.primal d.tangent

let unsupported_tangent primal msg =
  dual_pair primal (runtime_error msg)

let sample_primal = function
  | Distr1 (kind, e1) -> Distr1 (kind, dual_primal e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, dual_primal e1, dual_primal e2)

let rec primalize e =
  match Simplify.expr e with
  | ExprNode (Pair (p, _)) -> primalize p
  | ExprNode (Sample d) -> node (Sample (primalize_sample d))
  | ExprNode (Add (e1, e2)) -> add (primalize e1) (primalize e2)
  | ExprNode (Sub (e1, e2)) -> sub (primalize e1) (primalize e2)
  | ExprNode (Mul (e1, e2)) -> mul (primalize e1) (primalize e2)
  | ExprNode (Div (e1, e2)) -> div (primalize e1) (primalize e2)
  | ExprNode (SpecialFunc (name, args)) ->
      special name (List.map primalize args)
  | e' -> e'

and primalize_sample = function
  | Distr1 (kind, e1) -> Distr1 (kind, primalize e1)
  | Distr2 (kind, e1, e2) -> Distr2 (kind, primalize e1, primalize e2)

let unsupported_cdf dist point =
  dual_pair
    (node (Cdf (sample_primal dist, dual_primal point)))
    (runtime_error "differentiation of this CDF expression is not implemented")

let unsupported_cdf_expr kernel point =
  dual_pair
    (node (CdfExpr (primalize kernel, dual_primal point)))
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

let d_const f =
  { primal = const f; tangent = zero }

let d_add a b =
  { primal = add a.primal b.primal
  ; tangent = add a.tangent b.tangent
  }

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

let d_sqrt a =
  let primal = sqrt_ a.primal in
  { primal
  ; tangent = div a.tangent (mul two primal)
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

let rec contains_sample (ExprNode e) =
  match e with
  | Sample _ -> true
  | Const _ | Var _ | BoolConst _ | Nil | Unit
  | FinConst _ | RuntimeError _ -> false
  | Let (_, e1, e2) | Add (e1, e2) | Sub (e1, e2) | Mul (e1, e2)
  | Div (e1, e2) | Cmp (_, e1, e2, _) | FinCmp (_, e1, e2, _, _)
  | FinEq (e1, e2, _) | And (e1, e2) | Or (e1, e2) | Pair (e1, e2)
  | FuncApp (e1, e2) | Cons (e1, e2) | Assign (e1, e2) | Seq (e1, e2)
  | CdfExpr (e1, e2) ->
      contains_sample e1 || contains_sample e2
  | Not e1 | First e1 | Second e1 | Observe e1 | Ref e1 | Deref e1 ->
      contains_sample e1
  | Reset e1 -> contains_sample e1
  | Shift (_, e1) -> contains_sample e1
  | If (e1, e2, e3) ->
      contains_sample e1 || contains_sample e2 || contains_sample e3
  | Fun (_, e1) | Fix (_, _, e1) -> contains_sample e1
  | MatchList (e1, e2, _, _, e3) ->
      contains_sample e1 || contains_sample e2 || contains_sample e3
  | DiscreteCase cases ->
      List.exists
        (fun (b, p) -> contains_sample b || contains_sample p)
        cases
  | SpecialFunc (_, args) -> List.exists contains_sample args
  | Cdf (d, e1) -> contains_sample_sample d || contains_sample e1

and contains_sample_sample = function
  | Distr1 (_, e1) -> contains_sample e1
  | Distr2 (_, e1, e2) -> contains_sample e1 || contains_sample e2

let deterministic e =
  not (contains_sample e)

let const_value e =
  match Simplify.expr e with
  | ExprNode (Const f) -> Some f
  | _ -> None

let expr_equal e1 e2 =
  Simplify.expr e1 = Simplify.expr e2

let rec signed_linear_terms sign e =
  match Simplify.expr e with
  | ExprNode (Add (e1, e2)) ->
      signed_linear_terms sign e1 @ signed_linear_terms sign e2
  | ExprNode (Sub (e1, e2)) ->
      signed_linear_terms sign e1 @ signed_linear_terms (-sign) e2
  | e' -> [(sign, e')]

let sample_of_expr e =
  match Simplify.expr e with
  | ExprNode (Sample d) -> Some d
  | _ -> None

let d_scale sign d =
  if sign >= 0 then d else d_mul (d_const (-1.0)) d

let linear_sample_term sign term =
  match sample_of_expr term with
  | Some d -> Some (d_scale sign (d_const 1.0), d)
  | None ->
      (match Simplify.expr term with
       | ExprNode (Mul (e1, e2)) ->
           (match deterministic e1, sample_of_expr e2, deterministic e2, sample_of_expr e1 with
            | true, Some d, _, _ ->
                Some (d_scale sign (deterministic_dual e1), d)
            | _, _, true, Some d ->
                Some (d_scale sign (deterministic_dual e2), d)
            | _ -> None)
       | ExprNode (Div (e1, e2)) when deterministic e2 ->
           (match sample_of_expr e1 with
            | Some d ->
                Some
                  (d_scale sign (d_div (d_const 1.0) (deterministic_dual e2)), d)
            | None -> None)
       | _ -> None)

let try_gaussian_affine_cdf kernel point =
  let terms = signed_linear_terms 1 kernel in
  let rec loop gaussians offset = function
    | [] -> Some (List.rev gaussians, offset)
    | (sign, term) :: rest ->
        if deterministic term then
          loop gaussians (d_add offset (d_scale sign (deterministic_dual term))) rest
        else
          (match linear_sample_term sign term with
           | Some (coeff, Distr2 (DGaussian, mean, std)) ->
               let mean = deterministic_dual mean in
               let std = deterministic_dual std in
               loop ((coeff, mean, std) :: gaussians) offset rest
           | _ -> None)
  in
  match loop [] (d_const 0.0) terms with
  | Some (gaussians, offset) when gaussians <> [] ->
      let mean =
        List.fold_left
          (fun acc (coeff, mean, _) -> d_add acc (d_mul coeff mean))
          offset
          gaussians
      in
      let variance =
        sum_exprs
          (List.map
             (fun (coeff, _, std) -> square (mul coeff.primal std.primal))
             gaussians)
      in
      let variance_tangent =
        sum_exprs
          (List.map
             (fun (coeff, _, std) ->
                let cstd = d_mul coeff std in
                mul two (mul cstd.primal cstd.tangent))
             gaussians)
      in
      let std = d_sqrt { primal = variance; tangent = variance_tangent } in
      Some (gaussian_cdf (dual_expr mean) (dual_expr std) point)
  | _ -> None

let gamma_component_of_term sign term =
  match linear_sample_term sign term with
  | Some (coeff, Distr2 (DGamma, shape, scale)) ->
      (match const_value coeff.primal with
       | Some c when c > 0.0 ->
           let shape = deterministic_dual shape in
           let scale = deterministic_dual scale in
           Some (shape, d_mul coeff scale)
       | _ -> None)
  | Some (coeff, Distr1 (DExponential, rate)) ->
      (match const_value coeff.primal with
       | Some c when c > 0.0 ->
           let rate = deterministic_dual rate in
           Some (d_const 1.0, d_div coeff rate)
       | _ -> None)
  | _ -> None

let try_gamma_affine_sum_cdf kernel point =
  let terms = signed_linear_terms 1 kernel in
  let rec loop components offset = function
    | [] -> Some (List.rev components, offset)
    | (sign, term) :: rest ->
        if deterministic term then
          loop components (d_add offset (d_scale sign (deterministic_dual term))) rest
        else
          (match gamma_component_of_term sign term with
           | Some component -> loop (component :: components) offset rest
           | None -> None)
  in
  match loop [] (d_const 0.0) terms with
  | Some ((shape, scale) :: rest, offset) ->
      if List.for_all (fun (_, scale') -> expr_equal scale.primal scale'.primal) rest then
        let total_shape =
          List.fold_left
            (fun acc (shape, _) -> d_add acc shape)
            shape
            rest
        in
        let x = d_sub (dual point) offset in
        Some (gamma_cdf (dual_expr total_shape) (dual_expr scale) (dual_expr x))
      else
        None
  | _ -> None

type uniform_interval =
  { low : expr
  ; high : expr
  ; tangents : expr list
  }

let uniform_interval_of_term sign term =
  match linear_sample_term sign term with
  | Some (coeff, Distr2 (DUniform, lo, hi)) ->
      (match const_value coeff.primal with
       | Some c when c > 0.0 ->
           let lo = deterministic_dual lo in
           let hi = deterministic_dual hi in
           Some
             { low = mul coeff.primal lo.primal
             ; high = mul coeff.primal hi.primal
             ; tangents = [coeff.tangent; lo.tangent; hi.tangent]
             }
       | Some c when c < 0.0 ->
           let lo = deterministic_dual lo in
           let hi = deterministic_dual hi in
           Some
             { low = mul coeff.primal hi.primal
             ; high = mul coeff.primal lo.primal
             ; tangents = [coeff.tangent; lo.tangent; hi.tangent]
             }
       | _ -> None)
  | _ -> None

let subset_positive_sum y widths power =
  let rec loop parity acc = function
    | [] ->
        let sign = if parity mod 2 = 0 then 1 else -1 in
        [(sign, positive_pow acc power)]
    | width :: rest ->
        loop parity acc rest
        @ loop (parity + 1) (sub acc width) rest
  in
  loop 0 y widths

let try_uniform_affine_sum_cdf kernel point =
  let terms = signed_linear_terms 1 kernel in
  let rec loop intervals offset = function
    | [] -> Some (List.rev intervals, offset)
    | (sign, term) :: rest ->
        if deterministic term then
          loop intervals (d_add offset (d_scale sign (deterministic_dual term))) rest
        else
          (match uniform_interval_of_term sign term with
           | Some interval -> loop (interval :: intervals) offset rest
           | None -> None)
  in
  match loop [] (d_const 0.0) terms with
  | Some (intervals, offset) when intervals <> [] ->
      let x = dual point in
      let lows = List.map (fun interval -> interval.low) intervals in
      let widths =
        List.map (fun interval -> sub interval.high interval.low) intervals
      in
      let y = sub (sub x.primal offset.primal) (sum_exprs lows) in
      let n = List.length intervals in
      let width_product = product_exprs widths in
      let cdf_numer =
        signed_sum_exprs (subset_positive_sum y widths n)
      in
      let pdf_numer =
        signed_sum_exprs (subset_positive_sum y widths (n - 1))
      in
      let primal = div cdf_numer (mul (const (factorial n)) width_product) in
      let pdf = div pdf_numer (mul (const (factorial (n - 1))) width_product) in
      let nonpoint_tangents =
        offset.tangent
        :: List.concat (List.map (fun interval -> interval.tangents) intervals)
      in
      Some
        (require_zero_tangents primal "affine uniform sum" nonpoint_tangents (fun () ->
           dual_pair primal (mul pdf x.tangent)))
  | _ -> None

let rec parse_zero_uniform_product scale uniforms e =
  match Simplify.expr e with
  | ExprNode (Mul (e1, e2)) ->
      (match parse_zero_uniform_product scale uniforms e1 with
       | Some (scale', uniforms') -> parse_zero_uniform_product scale' uniforms' e2
       | None -> None)
  | ExprNode (Div (e1, e2)) when deterministic e2 ->
      (match parse_zero_uniform_product scale uniforms e1 with
       | Some (scale', uniforms') ->
           Some (d_div scale' (deterministic_dual e2), uniforms')
       | None -> None)
  | ExprNode (Sample (Distr2 (DUniform, lo, hi))) ->
      let lo = deterministic_dual lo in
      let hi = deterministic_dual hi in
      if is_zero_expr lo.primal then Some (scale, (lo, hi) :: uniforms)
      else None
  | _ when deterministic e ->
      Some (d_mul scale (deterministic_dual e), uniforms)
  | _ -> None

let product_unit_uniform_cdf z n =
  let log_term = neg (log_ z) in
  let series =
    List.init n (fun k -> div (pow_int log_term k) (const (factorial k)))
    |> sum_exprs
  in
  if_
    (node (Cmp (Le, z, zero, false)))
    zero
    (if_ (node (Cmp (Le, one, z, false))) one (mul z series))

let product_unit_uniform_pdf z n =
  let log_term = neg (log_ z) in
  let interior =
    div (pow_int log_term (n - 1)) (const (factorial (n - 1)))
  in
  if_
    (node (Cmp (Le, z, zero, false)))
    zero
    (if_ (node (Cmp (Le, one, z, false))) zero interior)

let try_zero_uniform_product_cdf kernel point =
  match parse_zero_uniform_product (d_const 1.0) [] kernel with
  | Some (scale, uniforms) when uniforms <> [] ->
      (match const_value scale.primal with
       | Some c when c <= 0.0 -> None
       | _ ->
           let x = dual point in
           let highs = List.map (fun (_, hi) -> hi.primal) uniforms in
           let support_scale = mul scale.primal (product_exprs highs) in
           let z = div x.primal support_scale in
           let n = List.length uniforms in
           let primal = product_unit_uniform_cdf z n in
           let pdf = div (product_unit_uniform_pdf z n) support_scale in
           let nonpoint_tangents =
             scale.tangent
             :: List.concat
                  (List.map (fun (lo, hi) -> [lo.tangent; hi.tangent]) uniforms)
           in
           Some
             (require_zero_tangents primal "product of zero-based uniforms" nonpoint_tangents (fun () ->
                dual_pair primal (mul pdf x.tangent))))
  | _ -> None

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
  match try_gaussian_affine_cdf kernel point with
  | Some result -> result
  | None ->
      (match try_gamma_affine_sum_cdf kernel point with
       | Some result -> result
       | None ->
           (match try_uniform_affine_sum_cdf kernel point with
            | Some result -> result
            | None ->
                (match try_zero_uniform_product_cdf kernel point with
                 | Some result -> result
                 | None -> unsupported_cdf_expr kernel point)))
