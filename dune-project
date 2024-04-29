(lang dune 3.12)

(name emltt)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name emltt)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune ppx_deriving)
 (tags
  (topics "effectful" "mltt")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
