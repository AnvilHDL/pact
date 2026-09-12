(lang dune 3.20)

(name pact)

(generate_opam_files true)

(source
 (github arj4web/pact))

(authors "Team Anvil")

(maintainers "Team Anvil")

(license MIT)

; (documentation https://url/to/documentation)

(package
 (name pact)
 (synopsis "An HDL that helps avoid mistakes")
 (description "Pact is an extension of anvil with a type system for communication safe hardware design.")
 (depends
  (ocaml (>= 4.14.0))
  (dune (>= 3.8))
  menhir
  yojson
 )
 (tags
  (hdl safety fpga))
 (version 0.1.0))

(using menhir 3.0)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
