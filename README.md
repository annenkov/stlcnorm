This projects includes:
* The proof of normalization of the Call-by-Value Simply-Typed Lambda
  Calculus (STLC) using Tait's method in Coq (with Martin Elsman).
* Implementation of nominal sets with applications to STLC (nominal
set of lambda terms, definition of alpha-equivalence, proof of
equivariance of the typing relation)
* Bi-directional type checking for STLC (with Étienne MIQUEY) - WIP.
* Intrinsically-typed System T (STLC with natural numbers). Features a denotation function on the intrinsic syntax allowing for "unquoting" syntactic expressions into Coq's definitions.
* An interpretation of the intrinsically-typed syntax of the STLC into a cartesian closed category using the Equations plugin for advanced pattern-matching on dependent types. It also features notations for "calculational proofs" similar to Lean and Agda. They allow for chaining several equational reasoning steps in an explicit manner.

Browse the docs
-----------
The html version is build using Coqdoc and CoqdocJS by Tobias Tebbi (https://github.com/tebbi/coqdocjs).

To get access to the html version follow this links:

* [Termination](http://dannenkov.me/stlcnorm/Stlc.stlc.html)
* [Nominal techniques](http://dannenkov.me/stlcnorm/Stlc.nomstlc.html)
* [Bi-directional type checking](http://dannenkov.me/stlcnorm/Stlc.stlc_bidir.html)
* [Incrisically-typed Goedel's System T](http://dannenkov.me/stlcnorm/Stlc.Goedel.html)
* [Interpretation of the intrisically-typed syntax of STLC into a cartisian-closed category](http://dannenkov.me/stlcnorm/Stlc.StlcCCC.html)

Usage
-----

Requires Coq 8.11.*, depends on the Equations plugin v1.2.3+8.11 and the Categories library by Amin Timany (https://github.com/amintimany/Categories).

Use `make` to build both source file in `Stlc` folder and html.
