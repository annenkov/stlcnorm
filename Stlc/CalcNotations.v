(** * Notation for reasoning using several transitive steps *)

(** This implementation uses several notations defined for different number of transitive steps. While it is not general and not very elegant, it currently works better than the one defined using Coq's recursive notations *)

Require Import PeanoNat.
Require Import ssreflect.
Import ssreflect.SsrSyntax.

Set Primitive Projections.

(** This way of writing proofs is inspired by Lean and also available in Agda. The current implementations is not as general as Lean/Agda and allows for chaining only equality steps. Ideally, it should support any transitive relation. *)

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 'end'" :=
  (@eq_trans _ a0 b0 b1 t0 t1) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 'end'" :=
  (@eq_trans _ a0 b0 b2 t0 (@eq_trans _ b0 b1 b2 t1 t2)) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 'end'" :=
  (@eq_trans _ a0 b0 _ t0 (@eq_trans _ b0 b1 _ t1 (@eq_trans _ b1 b2 b3 t2 t3))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 'end'" :=
  (@eq_trans _ a0 b0 b4 t0
             (@eq_trans _ b0 b1 b4 t1
                        (@eq_trans _ b1 b2 b4 t2 (@eq_trans _ b2 b3 b4 t3 t4)))) (at level 70, a0 at next level, only parsing) : calc_scope.


Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 ; '_' = b5 'by' t5 'end'" :=
  (@eq_trans _ a0 b0 _ t0
             (@eq_trans _ b0 b1 _ t1
                        (@eq_trans _ b1 b2 _ t2 (@eq_trans _ b2 b3 _ t3 (@eq_trans _ b3 b4 b5 t4 t5))))) (at level 70, a0 at next level, only parsing) : calc_scope.


(** ** Examples *)

Section Examples.

(** This is a notation for lifting rewriting tactic to the term level. It tries both directions and proves the goal by reflexivity afterwards *)
Notation "{{ f }}" := (ltac:((rewrite f;reflexivity) || (rewrite <-f; reflexivity))) (at level 70) : calc_scope.
Notation "{{ <-- f }}" := (ltac:((rewrite <-f; reflexivity))) (at level 70) : calc_scope.
Notation "{{ --> f }}" := (ltac:((rewrite f; reflexivity))) (at level 70) : calc_scope.


(** Terms, witnessing the equality steps (the part that goes after "by") can be built completely, or one can leave underscores and use [Program Definition] if necessary. Also, it is possible to use rewriting using the {{ some_lemma }} notation *)

(** This proof is complete and we don't need to use [Program Definition] *)

Open Scope calc_scope.

Definition ex_nat1 n m k : (n + m) + k = k + n + m :=
  calc (n + m) + k = k + (n + m) by Nat.add_comm _ _ ;
     _             = k + n + m  by Nat.add_assoc _ _ _
  end.

(** Note that the second item in the chain of steps starts with the underscore. This term usually can be inferred by Coq. We know that the this underscore must be filled-in with the "target" from the previous step, but there is no way to encode this due to the limitations of recursive notations in Coq *)

(** In this example we use underscores for all terms witnessing the steps *)
Program Definition ex_nat2 n m k : (n + m) + k = (m + k) + n :=
  calc (n + m) + k = n + (m + k) by _ ;
      _           = (m + k) + n by _
  end.
Next Obligation.
  symmetry. apply Nat.add_assoc.
Defined.
Next Obligation.
  apply Nat.add_comm.
Defined.

(** In this example we use use rewriting to prove steps by providing lemmas in double curly braces *)
Definition ex_nat3 n m k : n + (m + 0) + k = k + n + m :=
  calc n + (m + 0) + k = (n + m) + k by {{ plus_n_O }} ;
    _                  = k + (n + m) by {{ Nat.add_comm }} ;
    _                  = k + n + m by {{ Nat.add_assoc }}
end.

End Examples.