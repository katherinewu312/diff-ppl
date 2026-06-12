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
dune exec diff_ppl -- --ad FILE.slice
dune exec diff_ppl -- --ad-dual FILE.slice
dune exec diff_ppl -- --ad-dual --at theta=0.3 FILE.slice
```

Supports:

* plain discretization
* `--print-all` for source/normalized/typed/discretized output
* `--ad` for simplified gradient output
* `--print-all --ad` for raw + simplified gradient output
* `--ad-dual` for simplified dual output
* `--print-all --ad-dual` for raw + simplified dual output
* `--at PARAM=VALUE` for concrete evaluation for AD modes

`--ad` prints the ADEV-style tangent program for the discretized program.
`--ad-dual` prints the full dual program as `(primal, tangent)`.
With `--print-all`, AD modes also print the raw source-to-source AD program
before the simplified AD output.

AD modes also accept `--at PARAM=VALUE` or `--at=PARAM=VALUE`. This uses
`PARAM` as the differentiated variable, substitutes `VALUE` into the raw AD
program, and then simplifies the simplified AD program again at that concrete
point. Without `--at`, AD output is unchanged and still differentiates with
respect to `theta`.

## Project Layout

- `lib/`: Slice transformation library modules.
- `bin/main.ml`: CLI.
- `examples/`: sample `.slice` inputs.
- `test/`: OUnit tests for parsing, inference, and discretization.
