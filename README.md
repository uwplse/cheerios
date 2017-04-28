Cheerios
========

[![Build Status](https://api.travis-ci.org/uwplse/cheerios.svg?branch=master)](https://travis-ci.org/uwplse/cheerios)

Cheerios is a formally verified serialization library for Coq. It
defines a typeclass for serializable types and defines instances for
many built-in types. The specification of a serializable type requires
that serializing followed by deserializing is the identity.

Requirements
------------

- [`Coq 8.5`](https://coq.inria.fr/coq-85) or [`Coq 8.6`](https://coq.inria.fr/coq-86)
- [`StructTact`](https://github.com/uwplse/StructTact)

Usage
-----

Serializers for a type `A` are functions `A -> list bool`.  They are
easy to compose using list append.

Deserializers for a type `A` are written in the monad
`Cheerios.Deserializer.t`, which is a state monad over the binary data
with failure. Deserializers are easy to compose using monadic sequencing.

There is tactic automation (see `serialize_deserialize_id_crush`) for
proving that user-defined serializable types are correct. Proofs of
new serializers are typically just a few lines long.

Morphisms between serializable types describe binary-level
compatibility between the serialization format of two types. This
allows serializing something of type `A` and then safely deserializing
it at type `B`. There is also tactic automation for proving user-defined
morphisms.
