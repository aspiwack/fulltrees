Complete implementations
========================

Each file corresponds to a given section in the article:
- `simpl.ml` contains the code for the simple algorithm of Section 2
- `full.ml` contains the code for the assert-false-free implementation of Section 3
- `Full.v` contains the code for the Coq implementation of Section 4
- `Proof.v` contains the proofs of order preservation mentioned in the conclusion

All the file, except for `Proof.v`, are standalone. The files have been tested with Ocaml 3.12.1 and Coq 8.4pl2.

To run `Proof.v`, `Full.v` must be compiled first with the command `coqc Full.v` in the same directory. 