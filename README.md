Balancing lists: a proof pearl
==============================

Guyslain Naves & Arnaud Spiwack

Abstract
--------

Starting with an algorithm to turn lists into full trees which uses non-obvious invariants and partial functions, we progressively encode the invariants in the types of the data, removing most of the burden of a correctness proof.

The invariants are encoded using non-uniform inductive types which parallel numerical representations in a style advertised by Okasaki, and a small amount of dependent types.

Sources
-------

### Files ###

The source files containing the full programs in Ocaml and Coq can be found in the `src` repository.


### Building instructions ###

To build the article, you need to have a Latex distribution installed, as well as Ocaml (version 3.12 or later) and the melt text processing tool. The command line to run is `ocamlbuild fulltrees.pdf`. You can then find the pdf file in `_build/fulltrees.pdf`

### License ###

The content of this repository is distributed under Creative Commons licence [CC BY 3.0](http://creativecommons.org/licenses/by/3.0/).
