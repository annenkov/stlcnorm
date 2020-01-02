This projects includes:
* The proof of normalization of the Call-by-Value Simply-Typed Lambda
  Calculus (STLC) using Tait's method in Coq.
* Implementation of nominal sets with applications to STLC (nominal
set of lambda terms, definition of alpha-equivalence, proof of
equivariance of the typing relation)
* Bi-directional type checking for STLC (WIP).
* Intrinsically-typed System T (STLC with natural numbers). Features a denotation function on the intrisic syntax allowing for "unquiting" syntactic expressions into Coq's definitions.


Browse the docs
-----------
The html version is build using Coqdoc and CoqdocJS by Tobias Tebbi (https://github.com/tebbi/coqdocjs).

To get access to the html version follow this links:

* [Termination](http://dannenkov.me/stlcnorm/Stlc.stlc.html)
* [Nominal techniques](http://dannenkov.me/stlcnorm/Stlc.nomstlc.html)
* [Bi-directional type checking](http://dannenkov.me/stlcnorm/Stlc.stlc_bidir.html)
* [Incricically-typed Goedel's System T](http://dannenkov.me/stlcnorm/Stlc.Goedel.html)

Usage
-----

Requires Coq 8.9 and depends on the Equations plugin.

Use `make` to build both source file in `Stlc` folder and html.
