(** Primitive distributions. *)
module S = Symbolic

type t =
  | Bernoulli | Categorical
  | Uniform | Gaussian | Beta | Lognormal | Gamma | Pareto | Weibull
  | Gumbel1 | Gumbel2 | Exppow | Binomial
  | Exponential | Laplace | Cauchy | Tdist | Chi2 | Logistic | Rayleigh
  | Poisson

(** What a parameter must satisfy; checked as path requirements. *)
type domain = Real | Positive | Nonnegative | Probability | Natural

type signature =
  | Fixed of domain list  (** exactly these parameters *)
  | Repeated of domain    (** one or more parameters *)

(** Surface name, also used in reports. *)
let name = function
  | Bernoulli -> "flip" | Categorical -> "discrete"
  | Uniform -> "uniform" | Gaussian -> "gaussian" | Beta -> "beta"
  | Lognormal -> "lognormal" | Gamma -> "gamma" | Pareto -> "pareto"
  | Weibull -> "weibull" | Gumbel1 -> "gumbel1" | Gumbel2 -> "gumbel2"
  | Exppow -> "exppow" | Binomial -> "binomial"
  | Exponential -> "exponential" | Laplace -> "laplace" | Cauchy -> "cauchy"
  | Tdist -> "tdist" | Chi2 -> "chi2" | Logistic -> "logistic"
  | Rayleigh -> "rayleigh" | Poisson -> "poisson"

let signature = function
  | Bernoulli -> Fixed [Probability]
  | Categorical -> Repeated Probability
  | Uniform -> Fixed [Real; Real]
  | Gaussian | Lognormal | Gumbel1 | Gumbel2 -> Fixed [Real; Positive]
  | Beta | Gamma | Pareto | Weibull | Exppow -> Fixed [Positive; Positive]
  | Binomial -> Fixed [Probability; Natural]
  | Exponential | Laplace | Cauchy | Tdist | Chi2 | Logistic | Rayleigh ->
      Fixed [Positive]
  | Poisson -> Fixed [Nonnegative]

(** Every constructor, for name lookup. *)
let all = [
  Bernoulli; Categorical; Uniform; Gaussian; Beta; Lognormal; Gamma; Pareto;
  Weibull; Gumbel1; Gumbel2; Exppow; Binomial; Exponential; Laplace; Cauchy;
  Tdist; Chi2; Logistic; Rayleigh; Poisson;
]
let aliases = ["normal", Gaussian]

let of_name s =
  match List.find_opt (fun d -> name d = s) all with
  | Some d -> Some d
  | None -> List.assoc_opt s aliases

let accepts d count =
  match signature d with
  | Fixed domains -> List.length domains = count
  | Repeated _ -> count >= 1

let domain_requirements domain x =
  let zero = S.Number 0. in
  match domain with
  | Real -> []
  | Positive -> [S.binary S.Lt zero x]
  | Nonnegative -> [S.binary S.Le zero x]
  | Probability -> [S.binary S.Le zero x; S.binary S.Le x (S.Number 1.)]
  | Natural -> [S.binary S.Le zero x; S.is_integer x]

(** Requirements on [params] that make [d] well defined. *)
let requirements d params =
  let domains = match signature d with
    | Fixed domains -> domains
    | Repeated domain -> List.map (fun _ -> domain) params
  in
  let joint = match d, params with
    | Uniform, [a; b] -> [S.binary S.Le a b]
    | Categorical, ps ->
        (match List.fold_left (S.binary S.Add) (S.Number 0.) ps with
         | S.Number n when abs_float (n -. 1.) < 1e-12 -> []
         | sum -> [S.binary S.Eq sum (S.Number 1.)])
    | _ -> []
  in
  List.concat (List.map2 domain_requirements domains params) @ joint

(** Finite support with weights, for distributions the executor branches on. *)
let outcomes d params =
  match d, params with
  | Bernoulli, [p] ->
      Some [S.Boolean true, p; S.Boolean false, S.binary S.Sub (S.Number 1.) p]
  | Categorical, ps ->
      let n = List.length ps in
      Some (List.mapi (fun i p -> S.Finite (i, n), p) ps)
  | _ -> None

(** A draw known to equal a single term. *)
let point_mass d params =
  match d, params with
  | Uniform, [a; b] when a = b -> Some a
  | _ -> None
