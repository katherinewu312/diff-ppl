# diff-ppl: symbolic execution

This branch starts a new OCaml implementation of probabilistic symbolic
execution. Slice syntax is retained; there is no type-directed cut analysis,
CDF evaluation, inference circuit, or AD implementation in this branch yet.
The previous README is preserved in [docs/legacy-readme.md](docs/legacy-readme.md).
The mathematical writing and existing program inputs are retained.

## Build and run

Requires OCaml **4.13 or newer**, opam, Dune 3.11+, Menhir, and OUnit2 for tests.
GSL is no longer required.

```sh
opam install . --deps-only --with-test
eval "$(opam env)"
dune build
dune runtest
dune exec diff_ppl -- examples/symbolic/threshold.slice
```

Example input:

```ocaml
let u = uniform(0, 1) in
if u < theta then 1 else 0
```

Output identifies the kernel `sample#0 ~ uniform(0, 1)` and two paths:

```text
condition: (sample#0 < theta)
return: 1

condition: (sample#0 >= theta)
return: 0
```

Free identifiers are symbolic parameters. To substitute a concrete parameter:

```sh
dune exec diff_ppl -- --at theta=0.5 examples/symbolic/threshold.slice
```

Machine-readable output includes structured constraints, kernels, observations,
requirements, stores, and return expressions:

```sh
dune exec diff_ppl -- --json examples/symbolic/branch_threshold.slice
```

## Execution bounds

```sh
dune exec diff_ppl -- --max-recursion 16 --max-steps 10000 --max-paths 10000 examples/symbolic/recursion.slice
```

- `--max-recursion N`: maximum simultaneously active `fix` applications on a
  path (default 32). Base-case calls count too. Zero prohibits applying a
  recursive closure, but permits constructing one. This is an exploration
  bound, not a change to the program's return value.
- `--max-steps N`: expression evaluations along each path (default 10000).
  This also bounds divergence written using self-application without `fix`.
- `--max-paths N`: conservative exploration leaf budget (default 10000).
  Counts forks, including subsequently rejected paths. Exceeding it fails
  without emitting a partial result.

Recursion and step exhaustion produce explicit stopped paths and exit status
2. Runtime errors also produce stopped paths and status 2. Observation rejection
is a normal semantic outcome and does not make exploration incomplete. Successful
exploration exits 0. `complete` means exploration completed under these rules;
it does **not** mean all retained constraints are satisfiable or integrable.

## Source constructs

- Numbers, Booleans, arithmetic, comparisons, `&&`, `||`, `not`, and `if`.
- Lexically scoped `let`, higher-order `fun x -> body`, and application `f x`.
- Recursive functions `fix f x := body`, explored within the recursion bound.
- Pairs, `fst`, `snd`, `nil`, `::`, and list matching.
- References `ref e`, dereference `!r`, assignment `r := e`, and sequencing `;`.
- Hard observations `observe condition`; success returns unit, failure stops
  that path. Rejected paths remain in the report.
- `flip(p)` returns a Boolean; both outcomes are enumerated with their sampling
  kernel and outcome constraints. Known zero-probability outcomes are omitted.
- `discrete(p0, p1, ...)` returns `0#n`, `1#n`, etc.; finite comparisons use
  `==#n`, `<#n`, `<=#n`, `>#n`, and `>=#n`.
- All previously parsed named kernels: `uniform`, `gaussian`/`normal`,
  `exponential`, `beta`, `lognormal`, `gamma`, `laplace`, `cauchy`, `weibull`,
  `tdist`, `chi2`, `logistic`, `rayleigh`, `pareto`, `gumbel1`, `gumbel2`,
  `exppow`, `poisson`, and `binomial`. These are **recorded**, not sampled or
  integrated. Parameter order follows the existing Slice syntax; binomial is
  `binomial(p, n)`.

Use parentheses to make sequencing scope explicit, particularly inside `let`
and `if`. For example:

```ocaml
let r = ref 0 in
let ignored = (if flip(0.5) then r := 1 else r := 2) in
!r
```

## Semantics and scope

The executor uses call-by-value evaluation with symbolic scalar expressions,
lexical closures, a persistent store per path, and fresh identities for dynamic
sampling occurrences. Reusing a sampled value preserves its identity; separate
function calls that sample introduce distinct identities. Kernels may depend on
earlier samples. Branch-local kernels remain local to their paths.

Every unresolved control-flow condition splits execution, whether or not it is
parameter dependent. Boolean return queries are split too, including Boolean
components of pairs and lists. Numeric return expressions remain symbolic.
Compound expressions such as `x*x + y*y < theta` are preserved structurally.

Basic constant folding and direct predicate/complement checks prune some paths.
There is **no SMT solver**, support-aware feasibility checking, general region
simplification, integration, or differentiation. Retained paths may be infeasible.
Each path is an execution trace cylinder with its own sampling kernels; paths
can contain different samples. They are not yet a computed geometric partition
of one fixed-dimensional sample space.

Symbolic distribution validity conditions and nonzero-denominator requirements
are reported separately from path constraints. They are obligations on valid
executions, not extra observations and not probability weights. Later layers
must check/discharge them. Numeric invalid parameters are reported as errors.
Symbolic binomial trial counts carry an explicit `is_integer` requirement.
There is no static type
checking; concrete misuse is reported at execution time, while symbolic parameter
sort consistency is not currently checked.

## Architecture

1. **Layer 1 — symbolic operational semantics (implemented):** paths,
   constraints, observations, conditional sampling kernels, and symbolic returns.
2. **Layer 2 — region discovery (future):** feasibility, simplification,
   dependency grouping, boundaries, and supported region integrals.
3. **Layer 3 — differentiation semantics (future):** gradients of query
   integrals/normalized expectations, including moving-boundary contributions.

Probability masses suffice for region-constant queries. General numeric queries
require integrating the return expression as well. Hard observations require
normalization for conditional expectations. This executor preserves the
information needed for those later choices.

## Files

- `lib/ast.ml`: fresh source-only AST, without analysis-enriched types.
- `lib/parser.mly`, `lib/lexer.mll`, `lib/parse.ml`: retained syntax frontend,
  adapted for `flip`, arithmetic kernel parameters, unary minus, and nested comments.
- `lib/symbolic.ml`: symbolic expressions and elementary simplification.
- `lib/execute.ml`: bounded path exploration, closures, and persistent stores.
- `lib/report.ml`: readable output and structured JSON (schema version 1).
- `bin/main.ml`: file-based CLI.
- `test/test_symbolic.ml`: semantic regression tests.
- `examples/symbolic/`: focused examples for the new implementation.
- `tex/`, `TODO.md`, `docs/legacy-readme.md`: preserved writing. Legacy documents
  describe the previous implementation and are not the new engine's specification.

The previous compiler and experimental Python scripts remain available on
`main`. Pending changes that existed before this branch were saved in a retained
Git stash named `Preserve main work before symbolic-execution rewrite`; pending
example inputs were also copied onto this branch. No stash was dropped.
