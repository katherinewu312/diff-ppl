(** Numeric evaluation of probability expressions, using GSL.

    Distribution functions use GSL's parameterisations ([exponential] takes
    a rate). Integrals over continuous samples substitute u = F(x) and use
    adaptive quadrature; integer-valued samples are summed. Bernoulli and
    categorical draws never reach here: [Integrate] sums them out. *)
open Distribution
open Expr

(* Distribution functions *)

let unsupported d = invalid_arg ("No numeric density for " ^ name d)

(** Smallest closed interval containing the support. *)
let support d params =
  match d, params with
  | Uniform, [a;b] -> a, b
  | Beta, _ -> 0., 1.
  | (Exponential | Gamma | Poisson), _ -> 0., infinity
  | Binomial, [_;n] -> 0., n
  | Gaussian, _ -> neg_infinity, infinity
  | _ -> unsupported d

(** Density, or mass at [x] for integer-valued distributions. *)
let pdf d params x =
  let lo, hi = support d params in
  if x < lo || x > hi then 0. else
  let k = int_of_float x in
  match d, params with
  | Uniform, [a;b] -> Gsl.Randist.flat_pdf x ~a ~b
  | Gaussian, [m;s] -> Gsl.Randist.gaussian_pdf (x -. m) ~sigma:s
  | Exponential, [rate] -> Gsl.Randist.exponential_pdf x ~mu:(1. /. rate)
  | Beta, [a;b] -> Gsl.Randist.beta_pdf x ~a ~b
  | Gamma, [a;b] -> Gsl.Randist.gamma_pdf x ~a ~b
  | Poisson, [mu] -> if Float.is_integer x then Gsl.Randist.poisson_pdf k ~mu else 0.
  | Binomial, [p;n] ->
      if Float.is_integer x then Gsl.Randist.binomial_pdf k ~p ~n:(int_of_float n) else 0.
  | _ -> unsupported d

(** [P(X <= x)]. *)
let cdf d params x =
  let lo, hi = support d params in
  if x < lo || x = neg_infinity then 0. else if x >= hi || x = infinity then 1. else
  let k = int_of_float (floor x) in
  match d, params with
  | Uniform, [a;b] -> Gsl.Cdf.flat_P ~x ~a ~b
  | Gaussian, [m;s] -> Gsl.Cdf.gaussian_P ~x:(x -. m) ~sigma:s
  | Exponential, [rate] -> Gsl.Cdf.exponential_P ~x ~mu:(1. /. rate)
  | Beta, [a;b] -> Gsl.Cdf.beta_P ~x ~a ~b
  | Gamma, [a;b] -> Gsl.Cdf.gamma_P ~x ~a ~b
  | Poisson, [mu] -> Gsl.Cdf.poisson_P ~k ~mu
  | Binomial, [p;n] -> Gsl.Cdf.binomial_P ~k ~p ~n:(int_of_float n)
  | _ -> unsupported d

(** Inverse CDF of a continuous distribution, for [0 < p < 1]. *)
let quantile d params p =
  match d, params with
  | Uniform, [a;b] -> Gsl.Cdf.flat_Pinv ~p ~a ~b
  | Gaussian, [m;s] -> m +. Gsl.Cdf.gaussian_Pinv ~p ~sigma:s
  | Exponential, [rate] -> Gsl.Cdf.exponential_Pinv ~p ~mu:(1. /. rate)
  | Beta, [a;b] -> Gsl.Cdf.beta_Pinv ~p ~a ~b
  | Gamma, [a;b] -> Gsl.Cdf.gamma_Pinv ~p ~a ~b
  | _ -> unsupported d

(* Evaluation *)

exception Free_parameter of string

let () = Gsl.Error.init ()

(* GSL adaptive Gauss-Kronrod with known discontinuities [pts] (including
   both endpoints). When a tolerance cannot be met, GSL's best estimate is
   kept rather than raised. *)
let quadrature f pts =
  let ws = Gsl.Integration.make_ws 10000 in
  let strict = !Gsl.Error.handler in
  Gsl.Error.handler := (fun errno msg -> match errno with
    | Gsl.Error.EMAXITER | Gsl.Error.EROUND | Gsl.Error.ESING
    | Gsl.Error.EDIVERGE | Gsl.Error.ETOL -> ()
    | _ -> strict errno msg);
  Fun.protect ~finally:(fun () -> Gsl.Error.handler := strict) (fun () ->
    (Gsl.Integration.qagp f ~pts ~epsabs:1e-12 ~epsrel:1e-10 ws).Gsl.Fun.res)

(** Points in [lo, hi] where [state] changes, found on a grid and refined by
    bisection. *)
let changes state lo hi =
  let n = 64 and inset = 1e-12 *. (hi -. lo) in
  let at i =
    Float.min (hi -. inset) (Float.max (lo +. inset) (lo +. (hi -. lo) *. float i /. float n)) in
  let rec refine a b sa k =
    let m = 0.5 *. (a +. b) in
    if k = 0 then m else if state m = sa then refine m b sa (k-1) else refine a m sa (k-1)
  in
  List.concat (List.init n (fun i ->
    let a = at i and b = at (i+1) in
    let sa = state a in
    if sa = state b then [] else [refine a b sa 60]))

(** Indicator conditions not under a nested integral: the integrand's jumps. *)
let rec jumps = function
  | Indicator c -> [c]
  | Integral _ -> []
  | e -> fold_children (fun acc e -> acc @ jumps e) [] e

let summation d params f lo hi =
  let first = Float.max 0. (Float.ceil lo) in
  let rec go k acc =
    if k > hi || cdf d params (k -. 1.) >= 1. then acc
    else go (k +. 1.) (acc +. pdf d params k *. f k)
  in go first 0.

let rec eval env = function
  | Const c -> c
  | Param p | Indicator (Bool_param p) -> raise (Free_parameter p)
  | Var k -> List.assoc k env
  | Add (a,b) -> eval env a +. eval env b
  | Sub (a,b) -> eval env a -. eval env b
  | Mul (a,b) -> eval env a *. eval env b
  | Div (a,b) -> eval env a /. eval env b
  | Min (a,b) -> Float.min (eval env a) (eval env b)
  | Max (a,b) -> Float.max (eval env a) (eval env b)
  | Exp a -> Float.exp (eval env a)
  | Erf a -> Float.erf (eval env a)
  | Ceil a -> Float.ceil (eval env a)
  | Indicator c -> if holds env c then 1. else 0.
  | Cdf (d,ps,x) -> cdf d (List.map (eval env) ps) (eval env x)
  | Integral i ->
      let ps = List.map (eval env) i.parameters in
      let lo, hi = support i.distribution ps in
      let bound default = Option.fold ~none:default ~some:(eval env) in
      let lo = Float.max lo (bound neg_infinity i.lower) in
      let hi = Float.min hi (bound infinity i.upper) in
      let d = i.distribution in
      let f x = eval ((i.var,x) :: env) i.body in
      if Distribution.integer_valued d then summation d ps f lo hi
      else if lo >= hi then 0.
      else
        (* Substitute u = F(x): the range becomes finite and the density
           disappears. *)
        let ulo = cdf d ps lo and uhi = cdf d ps hi in
        let x u = quantile d ps u in
        let conditions = jumps i.body in
        let state u = List.map (holds ((i.var,x u) :: env)) conditions in
        let inner = if conditions = [] then [] else changes state ulo uhi in
        if uhi <= ulo then 0.
        else quadrature (fun u -> f (x u)) (Array.of_list ((ulo :: inner) @ [uhi]))
and holds env = function
  | Compare (op,a,b) -> Expr.holds op (eval env a) (eval env b)
  | Not c -> not (holds env c)
  | Bool_param p -> raise (Free_parameter p)

let value e = eval [] e
