(** * Tactic notation for reasoning using several transitive steps *)

(** Inspired by: http://geo2a.info/posts/2020-01-03-coq-equational-reasoning.html *)

Tactic Notation
  "calc" constr(lhs) "=" constr(rhs) "by" tactic(proof) :=  (stepl rhs by proof).

Tactic Notation
  "_" "=" constr(rhs) "by"  tactic(proof)  :=
  (stepl rhs by proof).

Tactic Notation
  "_" "=" constr(rhs) "by"  tactic(proof) "end" :=
  ((stepl rhs by proof);reflexivity).
