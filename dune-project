(lang dune 3.17)

(name tryCoq)

(generate_opam_files true)

(source
 (github kupl/tryCoq))

(authors "Mingyu Jo")

(maintainers "Mingyu Jo")

(license LICENSE)

(documentation https://github.com/kupl/tryCoq)

(package
 (name tryCoq)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
  (ocaml
   (>= 5.3.0))
  sexplib
  ppxlib
  ppx_sexp_conv
  containers
  core
  ocaml-compiler-libs
  ppx_deriving
  containers-data
  iter
  alcotest
  ocamldot
  ppx_inline_alcotest)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
