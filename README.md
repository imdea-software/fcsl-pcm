<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# The PCM library

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/imdea-software/fcsl-pcm/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/imdea-software/fcsl-pcm/actions?query=workflow:"Docker%20CI"




The PCM library provides a formalisation of Partial Commutative Monoids (PCMs),
a common algebraic structure used in separation logic for verification of
pointer-manipulating sequential and concurrent programs.

The library provides lemmas for mechanised and automated reasoning about PCMs
in the abstract, but also supports concrete common PCM instances, such as heaps,
histories, and mutexes.

This library relies on propositional and functional extentionality axioms.

## Meta

- Author(s):
  - Aleksandar Nanevski (initial)
  - Anton Trunov
  - Alexander Gryzlov
- License: [Apache-2.0](LICENSE)
- Compatible Coq versions: Coq 8.14 to 8.15
- Additional dependencies:
  - [MathComp ssreflect 1.13 to 1.15](https://math-comp.github.io)
- Coq namespace: `fcsl`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of The PCM library
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-fcsl-pcm
```

To instead build and install manually, do:

``` shell
git clone https://github.com/imdea-software/fcsl-pcm.git
cd fcsl-pcm
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Getting help

If you need assistance or would like to report a bug, drop us an email:
<fcsl@software.imdea.org> or open an [issue](https://github.com/imdea-software/fcsl-pcm/issues).

## History and context

More information can be obtained via the [FCSL web page](https://software.imdea.org/fcsl/).

An earlier version of this library was developed as a part of [Hoare type
theory](https://github.com/imdea-software/htt), which is now rebased on FCSL-PCM. The original
version of HTT can be found [here](https://software.imdea.org/~aleks/htt/).
