(** * Tactic notation for reasoning using several transitive steps *)

(** Inspired by: http://geo2a.info/posts/2020-01-03-coq-equational-reasoning.html *)

Require Import Arith.

Tactic Notation
  "calc" constr(lhs) "=" constr(rhs) "by" tactic(proof) :=  (stepl rhs by proof).

Tactic Notation
  "_" "=" constr(rhs) "by"  tactic(proof)  :=
  (stepl rhs by proof).

Tactic Notation
  "_" "=" constr(rhs) "by"  tactic(proof) "end" :=
  ((stepl rhs by proof);reflexivity).


Lemma ex_nat5 n m k: n + (m + 0) + k = k + n + m.
Proof.
  calc (n + (m + 0) + k) = ((n + m) + k) by now rewrite <- plus_n_O.
    _                    = (k + (n + m)) by now rewrite Nat.add_comm.
    _                    = (k + n + m) by now rewrite Nat.add_assoc
  end.
Qed.