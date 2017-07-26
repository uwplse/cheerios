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

Building from source
--------------------

Ensure that you have all the requirements installed.

```
./configure
make
```
