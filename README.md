# Cheerios

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/uwplse/cheerios/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/uwplse/cheerios/actions?query=workflow:"Docker%20CI"




A formally verified serialization library for Coq
which defines a typeclass for serializable types and instances
for many standard library types.

## Meta

- Author(s):
  - Justin Adsuara
  - Karl Palmskog
  - Keith Simmons (initial)
  - James R. Wilcox (initial)
  - Doug Woos (initial)
- License: [BSD 2-Clause "Simplified" license](LICENSE)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [StructTact](https://github.com/uwplse/StructTact)
- Coq namespace: `Cheerios`
- Related publication(s): none

## Building and installation instructions

The easiest way to build and install the Cheerios Coq library is via [opam](http://opam.ocaml.org/doc/Install.html):
```shell
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-cheerios
```

To instead build and install manually, do:
```shell
git clone https://github.com/uwplse/cheerios.git
cd huffman
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

To use serializable types in executable programs, code must be extracted
to OCaml and linked with the Cheerios runtime library. The connection between
the Coq definitions and the runtime library primitives is established in
`ExtractOCamlCheeriosBasic.v` in the `extraction` directory, which must be
imported before extraction of serializable types.

To build and install the OCaml runtime library:
```shell
opam pin add cheerios-runtime -k git https://github.com/uwplse/cheerios.git
```

To compile the runtime library manually, go to the `runtime` directory
and run `make` (requires [OCamlbuild](https://github.com/ocaml/ocamlbuild)).


