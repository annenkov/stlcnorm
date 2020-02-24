(** * Examples of calculational proof *)
Require Import CalcNotations.
Require Import Arith.

Section Examples.

(** This is a notation for lifting rewriting tactic to the term level. It tries both directions and proves the goal by reflexivity afterwards *)
Notation "{{ f }}" := (ltac:((rewrite f;reflexivity) || (rewrite <-f; reflexivity))) (at level 70) : calc_scope.
Notation "{{ <-- f }}" := (ltac:((rewrite <-f; reflexivity))) (at level 70) : calc_scope.
Notation "{{ --> f }}" := (ltac:((rewrite f; reflexivity))) (at level 70) : calc_scope.


(** Terms, witnessing the equality steps (the part that goes after "by") can be built completely, or one can leave underscores and use [Program Definition] if necessary. Also, it is possible to use rewriting using the {{ some_lemma }} notation *)

(** This proof is complete and we don't need to use [Program Definition] *)

Open Scope calc_scope.

Variables n m k a b : nat.

Definition ex_nat1 : (n + m) + k = k + n + m :=
  calc (n + m) + k = k + (n + m) by Nat.add_comm _ _ ;
     _             = k + n + m  by Nat.add_assoc _ _ _
  end.

(** Note that the second item in the chain of steps starts with the underscore. This term usually can be inferred by Coq. We know that the this underscore must be filled-in with the "target" from the previous step, but there is no way to encode this due to the limitations of recursive notations in Coq *)

(** In this example we use underscores for all terms witnessing the steps *)
Program Definition ex_nat2 : (n + m) + k = (m + k) + n :=
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
Definition ex_nat3 : n + (m + 0) + k = k + n + m :=
  calc n + (m + 0) + k = (n + m) + k by {{ plus_n_O }} ;
    _                  = k + (n + m) by {{ Nat.add_comm }} ;
    _                  = k + n + m by {{ Nat.add_assoc }}
end.

(** If more complex manipulations are required, the "ltac:()" notation can be used directly to justify the reasoning steps *)

Program Definition ex_nat4 : (a + b) * (a + b) = a^2 + 2*a*b + b^2 :=
  calc (a + b) * (a + b)
       = a*a + b*a + a*b + b*b by ltac:(ring);
    _  = a*a + 2*a*b + b*b by
       (* ltac:(let p := idtac in print p); *)
      ltac:(match goal with [_ : _ |- ?p] => fail 0 p end);
    _  = a^2 + 2*a*b + b^2 by ltac:(repeat rewrite Nat.pow_2_r;auto)
end.

End Examples.