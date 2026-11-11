# Boundary-analysis microbenchmarks

Eight small, hand-crafted programs isolate different problems in identifying
jump discontinuities. They use only scalar arithmetic, conditionals, bindings,
and independent uniform samples. They are synthetic feature tests, not ports of
literature benchmarks or a substitute for application-level evaluation.

Stable IDs RQ1-01 through RQ1-08 identify the cases; descriptive filenames
identify their primary features. The runner preserves this ID order. The
mathematical ground truth below is independent of Vela's solver statuses.

## Evaluation domain

Each sample ranges over the interior of its unit interval. The parameter
protocol is **0 < theta < 1**. Use the concrete assignments
**theta = 0.2, 0.4, 0.5, 0.6, 0.8**. These include the transitions in RQ1-04 and
the exceptional coincidence in RQ1-06.

For example, from the repository root:

```sh
dune exec diff_ppl -- --at theta=0.6 benchmarks/rq1/coincident.ppl
```

A separate symbolic-parameter experiment can use:

```sh
dune exec diff_ppl -- benchmarks/rq1/coincident.ppl
```

Symbolic runs leave `theta` unconstrained. Label these separately from the
concrete runs used to check the parameter-specific ground truth below.

## Run the suite

The Python runner builds the analyzer once and runs all `.ppl` files in this
directory sequentially. It uses only the Python standard library and can be
invoked from any working directory using its path.

```sh
# All eight programs, with symbolic theta; print the summary table.
python3 benchmarks/rq1/run.py

# Print retained equations, paths, and their assigned surface regions.
python3 benchmarks/rq1/run.py --boundaries

# Include extracted records that were subsequently dropped, with their reasons.
python3 benchmarks/rq1/run.py --boundaries all

# Concrete parameter sweep with repeated measurements; save one CSV.
python3 benchmarks/rq1/run.py --theta 0.2 0.4 0.5 0.6 0.8 --runs 5 --warmups 1
```

The table shows extracted/retained records, SAT, UNSAT, REDUNDANT, UNKNOWN,
and median elapsed seconds. Timing excludes the build and Python JSON parsing;
it includes analyzer startup, evaluation, refinement, and JSON output. Each
run starts a fresh analyzer process. Warmups can warm operating-system caches
but do not preserve the analyzer's in-memory SMT cache. The CSV also includes
minimum/maximum times and the run settings.

`--solver-timeout-ms` sets the timeout per SMT query (default 1000 ms).
`--timeout` limits each whole analyzer process (default 60 seconds). Errors
are reported separately from solver UNKNOWN results; the runner continues
through the suite and exits unsuccessfully if any case fails. Every run saves
one summary CSV to `benchmarks/rq1/results/rq1.csv` (overwritten each run);
use `--csv PATH` to write it elsewhere.

## Cases and ground truth

All surface descriptions concern jumps of the **final scalar output** at a
fixed parameter value. Magnitudes are absolute differences of one-sided
limits. Intersections of distinct surfaces are omitted from open surface
portions; coincident surfaces are counted once. Values exactly on a surface
are determined by the comparisons in the program.

| ID | File | Name and primary feature | Genuine jump surfaces |
|---|---|---|---|
| RQ1-01 | [threshold.ppl](threshold.ppl) | **Threshold payoff:** genuine jumps with nonconstant branch values | `s = theta`, magnitude `1 + theta`; `t = 0.6`, magnitude `2`. |
| RQ1-02 | [cancellation.ppl](cancellation.ppl) | **Canceled adjustment:** cancellation through later arithmetic, with other jumps preserved | `t = 0.4`, magnitude `4`; `u = 0.7`, magnitude `3`. No jump at `s = theta`. |
| RQ1-03 | [gated.ppl](gated.ppl) | **Gated outcomes:** boundaries restricted by execution paths | `s = theta` for `t < 0.3` (magnitude `1`) or `t > 0.7` (magnitude `2`); `t = 0.3` for `s < theta` (magnitude `1`); `t = 0.7` for `s > theta` (magnitude `2`). |
| RQ1-04 | [piecewise.ppl](piecewise.ppl) | **Threshold after a discontinuous update:** a conditional value in another guard | Exactly one jump, magnitude `1`: `s = theta` if `theta < 0.4`; `s = 0.4` if `0.4 <= theta <= 0.6`; `s = theta - 0.2` if `theta > 0.6`. |
| RQ1-05 | [infeasible.ppl](infeasible.ppl) | **Infeasible branches:** sample-support constraints and enclosing path conditions | `s = theta` for `t < 0.3`, and `t = 0.3` for `s < theta`; both have magnitude `1`. Other tests produce no jumps. |
| RQ1-06 | [coincident.ppl](coincident.ppl) | **Coincident thresholds:** scaled/reversed predicates and parameter-specific coincidence | If `theta != 0.6`: `s = theta`, magnitude `5`, and `s = 0.6`, magnitude `2`. If `theta = 0.6`: one surface `s = 0.6`, magnitude `7`. |
| RQ1-07 | [crossing.ppl](crossing.ppl) | **Intersecting surfaces:** a shared parametric diagonal under different path conditions | `t = s + theta/2` with `0 < s < theta/2`, magnitude `3`; `t = s + theta/2` with `theta/2 < s < theta`, magnitude `1`; `s = theta` with `t < 3 theta/2`, magnitude `1`; `t = theta` with `s > theta/2`, magnitude `2`. |
| RQ1-08 | [kinks.ppl](kinks.ppl) | **Continuous piecewise payoff:** nonconstant negative control | No jumps. Kinks occur at `s = theta`, `t = 0.4`, and `u = 0.5`. |

RQ1-02 is exactly equivalent to
`4 * indicator(t < 0.4) + 3 * indicator(u < 0.7)`: the final output does not
depend on `s` or `theta`. RQ1-08 equals
`min(s, theta) + max(t - 0.4, 0) + min(u, 1 - u)` and is continuous.
Here `indicator(P)` is 1 when P holds and 0 otherwise; it is explanatory
notation, not an additional language construct.
