(lang dune 3.11)
(using menhir 2.1)

(name diff_ppl)

(generate_opam_files true)

(license MIT)

(package
 (name diff_ppl)
 (synopsis "Transformation-only clone of Slice")
 (description "Parser, type inference, and discretization passes from Slice without backend emitters")
 (depends
  (ocaml (>= 4.08))
  (dune (>= 3.11))
  (menhir (>= 20201216))
  (gsl (>= 1.25))
  (ounit2 (>= 2.2.6)))
 (tags ("probabilistic-programming" "discretization" "ocaml")))
