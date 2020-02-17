(** * Notation for reasoning using several transitive steps *)

(** This implementation uses Coq's recursive notations (the ".." pattern). It works in simple cases, but using rewrites to fill the step witness fails sometimes when the terms have many implicit arguments. *)

Require Import PeanoNat List.
Require Import ssreflect.
Import ssreflect.SsrSyntax.


(** This way of writing proofs is inspired by Lean and also available in Agda. The current implementations is not as general as Lean/Agda and allows for chaining only equality steps. Ideally, it should support any transitive relation. *)

(** First, we have to pack the equality witness into a record, to be able to define a notation for each step in the proof. This is required due to limitations of recursive notations in Coq: only single variable is allowed to repeat *)
Record calc_item {A} :=
  mkCi { ci_src : A ;
    ci_tgt : A ;
    ci_pf : ci_src = ci_tgt}.

Definition comp_eq {A : Type} {a b c : A} : a = b -> b = c -> a = c.
intros p q. destruct p. exact q. Defined.

Definition eq_trans_up_to {A : Type} {x y0 y1 z : A} (p0 : y0 = y1)
  : x = y0 -> y1 = z -> x = z := (fun p q => @comp_eq _ _ _ _ p (comp_eq p0 q)).

(* Definition _src {A : Type} {a b : A} (p : a = b) := a. *)
(* Definition _tgt {A : Type} {a b : A} (p : a = b) := b. *)

Notation "a0 = b0 'by' t0" := (mkCi _ a0 b0 t0) (at level 70, b0 at next level): calc_scope.
(* Notation "a0 = b0 'by' t0" := (t0 : a0 = b0) (at level 70, b0 at next level): calc_scope. *)

Notation "'smp' t" := (let p:=t in
                       ltac: (match goal with
                        | [p := ?t |- _] => cbn in p;exact t
                        end)) (at level 70).
Import ListNotations.

Notation "'calc' ci0 ; .. ; cin 'end'" :=
  (@eq_trans_up_to _ (ci_src ci0) (ci_tgt ci0) _ _ eq_refl (ci_pf ci0)
                   ( .. (@eq_trans_up_to _ (ci_src cin) (ci_tgt cin) _ _ eq_refl (ci_pf cin) eq_refl ) .. )).

(* Notation "'calc' ci0 ; .. ; cin 'end'" := *)
(*   (@eq_trans_up_to _ (_src ci0) (_tgt ci0) _ _ eq_refl ci0 ( .. (@eq_trans_up_to _ (_src cin) (_tgt cin) _ _ eq_refl cin eq_refl ) .. )). *)


(** Notations for lifting the rewriting tactic to the term level. It tries both directions and proves the goal by reflexivity afterwards *)
Notation "{{ f }}" := (ltac:((rewrite f;reflexivity) || (rewrite <-f; reflexivity))) (at level 70).
Notation "{{ <- f }}" := (ltac:((rewrite <-f; reflexivity))) (at level 70).
Notation "{{ -> f }}" := (ltac:((rewrite f; reflexivity))) (at level 70).

(** ** Examples *)

(** Terms, witnessing the equality steps (the part that goes after "by") can be built completely, or one can leave underscores and use [Program Definition] if necessary. Also, it is possible to use rewriting using the {{ some_lemma }} notation *)

Open Scope calc_scope.

(** This proof is complete and we don't need to use [Program Definition] *)
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
