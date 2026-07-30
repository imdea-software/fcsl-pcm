<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# The PCM library

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/imdea-software/fcsl-pcm/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/imdea-software/fcsl-pcm/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



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
- Rocq-community maintainer(s):
  - Alexander Gryzlov ([**@clayrat**](https://github.com/clayrat))
- License: [Apache-2.0](LICENSE)
- Compatible Rocq/Coq versions: 9.2 or later
- Additional dependencies:
  - [MathComp ssreflect 2.6 or later](https://math-comp.github.io)
  - [Hierarchy Builder 1.7.0 or later](https://github.com/math-comp/hierarchy-builder)
  - [MathComp algebra](https://math-comp.github.io)
- Rocq/Coq namespace: `pcm`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of The PCM library
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-fcsl-pcm
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/imdea-software/fcsl-pcm.git
cd fcsl-pcm
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
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
