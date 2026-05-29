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

The executable accepts one input file:

```sh
dune exec diff_ppl -- FILE.slice
dune exec diff_ppl -- --print-all FILE.slice
```

## Project Layout

- `lib/`: Slice transformation library modules.
- `bin/main.ml`: transformation-only command-line entry point.
- `examples/`: sample `.slice` inputs.
- `test/`: OUnit tests for parsing, inference, and discretization.

## Notes

- Backend files from Slice are intentionally omitted: `to_dice.ml`,
  `to_roulette.ml`, and `to_mc.ml`.
- The main library is exposed to Dune as `diff_ppl.slice`; the OCaml module name
  remains `Slice`.
