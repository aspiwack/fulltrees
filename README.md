Balancing lists: a proof pearl
==============================

Abstract
--------

Starting with an algorithm to turn lists into full trees which uses non-obvious invariant and partial functions, we progressively encode the invariants in the types of the data, removing most of the burden of a correctness proof.


Files
-----

The source files containing the full programs in Ocaml and Coq can be found in the `src` repository.


Building instructions
---------------------

To build the article, you need to have a Latex distribution installed, as well as Ocaml (version 3.12 or later) and the melt text processing tool. The command line to run is `ocamlbuild -classic-display fulltrees.pdf`. You can then find the pdf file in `_build/fulltrees.pdf`