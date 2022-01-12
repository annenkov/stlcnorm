(** * Notation for reasoning using several transitive steps (recursive) *)

(** Inspired by this: https://gist.github.com/gallais/f046bcc2c348c5fed5e9 *)

(** This notation is similar to [CalcNotations.v], but works for any number of transitive steps. However, it fails when one needs to use rewrites or, say ring, because we want to avoid writing the "middle points" when we use the notation. E.g. we write [_ = b by p] for all the steps excluding the first one. They can be ommitted because we know that the previous equation "end" coincudes with the "start" of the current one, since we build a chain of transitive steps. Usually, these "middle points" can be inferred by Coq, but if we use [ltac:()] to build terms witnessing the transitivity steps, the "middle points" might be not resolved yet and the tactics in the [ltac:()] call might fail.   *)

Notation "'calc' p" := p (at level 70, right associativity) : calc_scope.
Notation "a = b 'by' p ; pr" := (@eq_trans _ a b _ p pr) (at level 70, b at next level, right associativity) : calc_scope.
Notation "a = b 'by' p 'end'" := (@eq_trans _ _ b b p (@eq_refl _ b)) (b at next level, at level 70): calc_scope.
