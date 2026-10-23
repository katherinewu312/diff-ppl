(lang dune 3.11)
(using menhir 2.1)

(name diff_ppl)

(generate_opam_files true)

(license MIT)

(package
 (name diff_ppl)
 (synopsis "Symbolic execution of higher-order probabilistic programs")
 (description "Bounded symbolic operational semantics for Slice programs")
 (depends
  (ocaml (>= 4.13))
  (dune (>= 3.11))
  (menhir (>= 20201216))
  (ounit2 (>= 2.2.6)))
 (tags ("probabilistic-programming" "discretization" "ocaml")))
