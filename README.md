# diff-ppl

`diff-ppl` is a transformation from a continuous PPL to a discrete PPL.

## Requirements

- OCaml 4.08 or newer
- opam
- Dune 3.11 or newer
- Menhir
- GNU Scientific Library (GSL)
- OUnit2, for tests

The OCaml `gsl` package needs the system GSL library installed first.

On macOS with Homebrew:

```sh
brew install gsl pkg-config
```

On Ubuntu/Debian:

```sh
sudo apt-get update
sudo apt-get install libgsl-dev pkg-config
```

## Install Dependencies

From the project root:

```sh
opam install . --deps-only --with-test
eval "$(opam env)"
```

If you prefer installing packages explicitly:

```sh
opam install dune menhir gsl ounit2
eval "$(opam env)"
```

## Build

```sh
dune build
```

Clean builds may print Menhir warnings inherited from the original Slice parser
grammar. Those warnings do not prevent the project from building.

## Test

```sh
dune runtest
```

## Run

Transform a Slice program into its discretized Slice program:

```sh
dune exec diff_ppl -- examples/simple_test.slice
```

Print the source program, typed AST, and transformed program:

```sh
dune exec diff_ppl -- --print-all examples/simple_test.slice
```

The executable accepts one input file, e.g.:

```sh
dune exec diff_ppl -- FILE.slice
dune exec diff_ppl -- --print-all FILE.slice
dune exec diff_ppl -- --expect FILE.slice
dune exec diff_ppl -- --ad FILE.slice
dune exec diff_ppl -- --ad-dual FILE.slice
dune exec diff_ppl -- --ad-dual --at theta=0.3 FILE.slice
dune exec diff_ppl -- --ad-dual theta=0.5 alpha=0.2 FILE.slice
dune exec diff_ppl -- --reverse --ad-dual theta=0.5 alpha=0.2 FILE.slice
dune exec diff_ppl -- --ad-dual theta=0.5 dtheta=1 alpha=0.2 dalpha=1 FILE.slice
dune exec diff_ppl -- --reverse --ad-dual theta=0.5 dtheta=1 alpha=0.2 dalpha=1 FILE.slice
```

Supports:

* plain discretization
* `--print-all` for source/normalized/typed/discretized output
* `--expect` for evaluation/expectation of the program
* `--ad` for simplified gradient output
* `--print-all --ad` for raw + simplified gradient output
* `--ad-dual` for simplified dual output
* `--print-all --ad-dual` for raw + simplified dual output
* `--forward` or `--reverse` to choose AD mode; forward is the default if no flag is specified
* `--at PARAM=VALUE` for concrete evaluation for AD modes
* `PARAM=VALUE` for concrete substitution and `dPARAM=SEED` for explicit seeding

For forward mode, when no explicit `dPARAM=SEED` assignments are provided,
`--ad` prints the full gradient vector for all free float input variables, and
`--ad-dual` prints `(expected_value, gradient_vector)`. The vector entries are
ordered by variable name. If explicit `dPARAM=SEED` assignments are provided,
forward mode gives a scalar directional derivative: `--ad`
prints the seeded tangent and `--ad-dual` prints `(primal, tangent)`.
With `--print-all`, AD modes also print the raw source-to-source AD program
before the simplified AD output.

**** It is best to give a concrete PARAM=VALUE at runtime. Even though symbolic expressions like theta -> d/dtheta E[X(theta)] _can_ be produced, such expressions may not always be correct (i.e. the ordering of the cuts of an expression may get messed up, causing problems in the discretization and hence the AD transformation). ****

*** Currently, every differentiable input variable is assumed to be a scalar float.

AD modes also accept `--at PARAM=VALUE` or `--at=PARAM=VALUE`. This uses
`VALUE` when ordering symbolic discretization cuts, substitutes `VALUE` into
the raw AD program, and then simplifies the simplified AD program again at that
concrete point.

AD modes can also accept bare assignments before the input file. `PARAM=VALUE`
substitutes a concrete value, and `dPARAM=SEED` sets the AD seed for `PARAM`.
If explicit `dPARAM=SEED` assignments are provided, unspecified variables get
seed `0`. In forward mode, if no explicit seeds are provided, all free float
variables are seeded one at a time to produce the gradient vector.

## Project Layout

- `lib/`: Slice transformation library modules.
- `bin/main.ml`: CLI.
- `examples/`: sample `.slice` inputs.
- `test/`: OUnit tests for parsing, inference, and discretization.
