(** Source syntax only *)
type cmp_op = Lt | Le

type 'a expr_generic =
  | Var of string | Const of float | BoolConst of bool
  | Let of string * 'a * 'a | Sample of 'a sample
  | DiscreteCase of ('a * 'a) list | Flip of 'a
  | Cmp of cmp_op * 'a * 'a * bool
  | And of 'a * 'a | Or of 'a * 'a | Not of 'a
  | If of 'a * 'a * 'a
  | Pair of 'a * 'a | First of 'a | Second of 'a
  | Fun of string * 'a | FuncApp of 'a * 'a
  | FinConst of int * int
  | FinCmp of cmp_op * 'a * 'a * int * bool | FinEq of 'a * 'a * int
  | Observe of 'a | Fix of string * string * 'a
  | Nil | Cons of 'a * 'a
  | MatchList of 'a * 'a * string * string * 'a
  | Ref of 'a | Deref of 'a | Assign of 'a * 'a | Seq of 'a * 'a | Unit
  | Add of 'a * 'a | Sub of 'a * 'a | Mul of 'a * 'a | Div of 'a * 'a
and single_arg_dist_kind =
  | DExponential | DLaplace | DCauchy | DTDist | DChi2 | DLogistic
  | DRayleigh | DPoisson
and two_arg_dist_kind =
  | DUniform | DGaussian | DBeta | DLogNormal | DGamma | DPareto | DWeibull
  | DGumbel1 | DGumbel2 | DExppow | DBinomial
and 'a sample =
  | Distr1 of single_arg_dist_kind * 'a
  | Distr2 of two_arg_dist_kind * 'a * 'a

type expr = ExprNode of expr expr_generic

let distribution1_name = function
  | DExponential -> "exponential" | DLaplace -> "laplace"
  | DCauchy -> "cauchy" | DTDist -> "tdist" | DChi2 -> "chi2"
  | DLogistic -> "logistic" | DRayleigh -> "rayleigh" | DPoisson -> "poisson"

let distribution2_name = function
  | DUniform -> "uniform" | DGaussian -> "gaussian" | DBeta -> "beta"
  | DLogNormal -> "lognormal" | DGamma -> "gamma" | DPareto -> "pareto"
  | DWeibull -> "weibull" | DGumbel1 -> "gumbel1" | DGumbel2 -> "gumbel2"
  | DExppow -> "exppow" | DBinomial -> "binomial"
