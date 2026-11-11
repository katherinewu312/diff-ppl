# Expectation gradients

From the repository root:

```sh
python3 gradient/estimate.py examples/symbolic/threshold.ppl --at theta=0.4 --draws 1000 --seed 0
```

For `.ppl` inputs, the command runs the analyzer automatically, keeping parameters
symbolic and passing its JSON directly to the estimator. Existing JSON reports
can also be supplied instead of a program. **Keep parameters symbolic when
generating those reports:** the analyzer's `--at` loses derivatives.
Repeat the estimator's `--at` for multiple parameters. Output contains the total,
interior, and boundary estimates in a concise text summary, each with a Monte
Carlo standard error.

### Testing
```
python3 -m unittest gradient.test_estimate -v
```

### Choosing an integration backend

The default `--backend mc` retains Monte Carlo integration and requires only the
Python standard library. Install the optional exact dependency with:

```sh
python3 -m pip install -r gradient/requirements-exact.txt
```

Then select the backend explicitly:

```sh
python3 gradient/estimate.py examples/symbolic/threshold.ppl --at theta=0.4 --backend exact
python3 gradient/estimate.py examples/symbolic/threshold.ppl --at theta=0.4 --backend auto --draws 1000
python3 gradient/estimate.py examples/symbolic/threshold.ppl --at theta=0.4 --backend mc --draws 1000
```

- `exact`: compute exact symbolic interior, boundary, and total gradients, or fail
  with an unsupported-case explanation. Output includes a decimal approximation,
  not a Monte Carlo standard error. `--draws` and `--seed` are unused.
- `auto`: try exact integration, then use Monte Carlo if the exact backend does
  not support the program or SymPy is unavailable. Prints the fallback reason.
- `mc`: always use the existing Monte Carlo estimator.

The exact backend supports unbranched polynomial outputs with any number of
independent Uniform/Gaussian base samples, and piecewise-polynomial outputs with
one base sample and affine guards. Nested branches and Boolean guards are allowed
within the estimator's existing validation rules. Uniform integrals use rational
arithmetic; Gaussian integrals use exact moments and truncated-moment recurrences,
with results expressed using `exp`, `sqrt`, and `erf` as necessary. Parameters are
differentiated before their exact supplied values are substituted (`0.4` means
`2/5`; rational inputs such as `theta=2/5` also work).

Branching with multiple base samples, including multivariate Uniform polytopes,
is not yet supported by `exact`. The existing restrictions on degenerate guards,
coincident surfaces, and Uniform support faces still apply to all backends.
Analyzer JSON schemas 3 and 5 are accepted; integration uses the original `value`
expression and its guards.

The Python API accepts `Estimator(report, parameters).estimate(backend="exact")`.
Exact result entries contain `exact` (a symbolic string) and `mean` (a decimal
approximation); MC entries retain `mean` and `standard_error`. The top-level
`backend` field identifies the method actually used.

Run both backend suites after installing the optional dependency:

```sh
python3 -m unittest gradient.test_estimate gradient.test_exact -v
```
