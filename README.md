# Boundaries

## Run

Requires OCaml 4.13+, Dune 3.11+, Menhir, and **Z3 on PATH**. OUnit2 is used for
regression tests. 

```sh
opam install . --deps-only --with-test
eval "$(opam env)"
dune build
dune runtest
dune exec diff_ppl -- examples/symbolic/threshold.slice
```

For your own file:

```sh
dune exec diff_ppl -- YOUR_PROGRAM.slice
```

Pass in an assignment:

```sh
dune exec diff_ppl -- --at theta=0.5 YOUR_PROGRAM.slice
```

Z3 has a timeout for each query (default 1000 milliseconds):

```sh
dune exec diff_ppl -- --solver-timeout-ms 2000 YOUR_PROGRAM.slice
```

NOTE: program must return some real value.

## Example

```ocaml
let u = uniform(0,1) in
if u < theta then 1 else 0
```

The analyzer produces:

```text
v = ite(s1 < theta, 1, 0)
B = {(true; s1 - theta; 1; 0)}
```

The base variable satisfies `0 < s1 < 1`. Solving checks
`0 < s1 < 1 && s1 - theta = 0 && 1 != 0`, which is SAT for some theta, so this is retained. With a concrete theta outside the support, reachability
selects one branch and no candidate is generated.