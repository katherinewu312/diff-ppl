(lang dune 3.11)
(using menhir 2.1)

(name diff_ppl)

(generate_opam_files true)

(license MIT)

(package
 (name diff_ppl)
 (synopsis "Boundary analysis of higher-order recursive probabilistic programs")
 (description "Implementation of the symbolic analysis and boundary queries in tex/main.tex")
 (depends
  (ocaml (>= 4.13))
  (dune (>= 3.11))
  (menhir (>= 20201216))
  (ounit2 (>= 2.2.6)))
 (tags ("probabilistic-programming" "discretization" "ocaml")))
