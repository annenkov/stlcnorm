(** * Notation for reasoning using several transitive steps (recursive) *)

Require Import Arith.
(** Inspired by this: https://gist.github.com/geo2a/31381aeb345c789761504da1b5d42168 *)

(** This notation is similar to [CalcNotations.v], but works for any number of transitive steps. However, it fails when one needs to use rewrites or, say ring, because we want to avoid writing the "middle points" when we use the notation. E.g. we write [_ = b by p] for all the steps excluding the first one. They can be ommitted because we know that the previous equation "end" coincudes with the "start" of the current one, since we build a chain of transitive steps. Usually, these "middle points" can be inferred by Coq, but if we use [ltac:()] to build terms witnessing the transitivity steps, the "middle points" might be not resolved yet and the tactics in the [ltac:()] call might fail.   *)

Notation "'calc' p" := p (at level 70, right associativity) : calc_scope.
Notation "a = b 'by' p ; pr" := (@eq_trans _ a b _ p pr) (at level 70, b at next level, right associativity) : calc_scope.
Notation "a = b 'by' p 'end'" := (@eq_trans _ _ b b p (@eq_refl _ b)) (b at next level, at level 70): calc_scope.

Open Scope calc_scope.

(** In this example, [ltac:(ring)] cannot solve the steps because the "middle points" are still uninstantiated existential variables. One can see the goal that [ltac:()] sees by using this tactic expression:ltac:(match goal with [_ : _ |- ?p] => fail 0 p end); *)
Fail Definition ex_nat_ring_fail a b : (a + b) * (a + b) = a^2 + 2*a*b + b^2 :=
  calc (a + b) * (a + b)
       = a*a + b*a + a*b + b*b by ltac:(ring);
    _  = a*a + 2*a*b + b*b by ltac:(ring);
    _  = a^2 + 2*a*b + b^2 by ltac:(repeat rewrite Nat.pow_2_r;auto)
end.

(** But it's absolutely fine to leave underscores in place of proofs and fill them in later *)
Program Definition ex_nat_ring_success a b : (a + b) * (a + b) = a^2 + 2*a*b + b^2 :=
  calc (a + b) * (a + b)
       = a*a + b*a + a*b + b*b by ltac:(ring);
    _  = a*a + 2*a*b + b*b by _;
    _  = a^2 + 2*a*b + b^2 by ltac:(repeat rewrite Nat.pow_2_r;auto)
end.
Next Obligation.
  ring.
Qed.
