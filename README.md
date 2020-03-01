# Buchberger

[![Travis][travis-shield]][travis-link]

[travis-shield]: https://travis-ci.com/palmskog/buchberger.svg?branch=master
[travis-link]: https://travis-ci.com/palmskog/buchberger/builds




A machine-checked implementation of Buchberger's algorithm,
which computes the Gröbner basis associated with a polynomial ideal.

## Meta

- Author(s):
  - Laurent Théry (initial)
  - Henrik Persson (initial)
- License: [GNU Lesser General Public License v2.1](LICENSE)
- Compatible Coq versions: 8.7 or later
- Additional dependencies: none
- Coq namespace: `Buchberger`
- Related publication(s):
  - [A machine checked implementation of Buchberger's algorithm](https://link.springer.com/article/10.1023/A:1026518331905) doi:[10.1023/A:1026518331905](https://doi.org/10.1023/A:1026518331905)

## Building and installation instructions

The easiest way to install the latest released version of Buchberger
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-buchberger
```

To instead build and install manually, do:

``` shell
git clone https://github.com/palmskog/buchberger
cd buchberger
make   # or make -j <number-of-cores-on-your-machine>
make install
```


## Documentation

This project contains a Coq formalization of Buchberger's algorithm.

It is composed of:
- A proof of correctness of the algorithm as described in
A machine checked implementation of Buchberger's algorithm, JAR, January 2001.
- An implementation of the algorithm. With respect to the paper,
terms are not abstracted but built directly from coef and monomials.
- A constructive proof of Dickson's lemma due to Henrik Persson.

In `Extract.v`, it is explained how the extracted code found in
`sin_num.ml` can be used to compute Gröbner bases.