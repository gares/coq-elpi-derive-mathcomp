<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Coq-Elpi's deride for MathComp

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/gares/elpi-derive-mathcomp/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/gares/elpi-derive-mathcomp/actions?query=workflow:"Docker%20CI"




This package links the derivations in `elpi.apps.derive` to
structures of the Mathematical Components library.

## Meta

- Author(s):
  - Enrico Tassi (initial)
  - Jean-Christophe Lechenet (initial)
- License: [MIT](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io)
  - [Coq-Elpi](https://github.com/LPCIC/coq-elpi) >= 1.16
- Coq namespace: `elpi.apps.derive.mathcomp`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Coq-Elpi's deride for MathComp
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-elpi-derive-mathcomp
```

To instead build and install manually, do:

``` shell
git clone https://github.com/gares/elpi-derive-mathcomp.git
cd elpi-derive-mathcomp
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Usage

```coq
From elpi.apps Require Import derive.mathcomp.std.

From mathcomp Require Import ssrbool ssrfun eqtype.

#[only(eqType)] derive nat.

Check forall x : nat, x == x.
```
