<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Buchberger

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/buchberger/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/buchberger/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



A verified implementation of Buchberger's algorithm in Coq,
which computes the Gröbner basis associated with a polynomial ideal.
Also includes a constructive proof of Dickson's lemma.

## Meta

- Author(s):
  - Laurent Théry (initial)
  - Henrik Persson (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Coq versions: 8.12 or later
- Additional dependencies:
  - [Equations](https://github.com/mattam82/Coq-Equations) 1.2 or later
- Coq namespace: `Buchberger`
- Related publication(s):
  - [A machine checked implementation of Buchberger's algorithm](https://link.springer.com/article/10.1023/A:1026518331905) doi:[10.1023/A:1026518331905](https://doi.org/10.1023/A:1026518331905)
  - [An Integrated Development of Buchberger's Algorithm in Coq](https://hal.inria.fr/inria-00072316/) 
  - [Gröbner Bases in Type Theory](https://link.springer.com/chapter/10.1007/3-540-48167-2_3) doi:[10.1007/3-540-48167-2_3](https://doi.org/10.1007/3-540-48167-2_3)

## Building and installation instructions

The easiest way to install the latest released version of Buchberger
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-buchberger
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/buchberger.git
cd buchberger
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

This project contains a Coq formalization of Buchberger's algorithm.
It is composed of:
- A proof of correctness of the algorithm as described in
 [A machine checked implementation of Buchberger's algorithm][jar-url],
 Journal of Automated Reasoning, January 2001.
- An implementation of the algorithm. With respect to the paper,
  terms are not abstracted but built directly from coef and monomials.
- A constructive proof of Dickson's lemma due to Henrik Persson.

In the file `Extract.v`, it is explained how the extracted code found in
`sin_num.ml` can be used to compute Gröbner bases.

## Related work

An alternative formalization of Gröbner bases in Coq using the SSReflect
proof language and the Mathematical Components library is available
[elsewhere][grobner-url].

[jar-url]: https://link.springer.com/article/10.1023/A:1026518331905
[grobner-url]: https://github.com/thery/grobner
