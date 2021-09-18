(** * Notation for reasoning using several transitive steps (recursive) *)

(** Inspired by this: https://gist.github.com/gallais/f046bcc2c348c5fed5e9 *)

(** This notation is similar to [CalcNotations.v], but works for any number of transitive steps. However, it fails when one needs to use rewrites or, say ring, because we want to avoid writing the "middle points" when we use the notation. E.g. we write [_ = b by p] for all the steps excluding the first one. They can be omitted because we know that the previous equation "end" coincides with the "start" of the current one, since we build a chain of transitive steps. Usually, these "middle points" can be inferred by Coq, but if we use [ltac:()] to build terms witnessing the transitivity steps, the "middle points" might be not resolved yet and the tactics in the [ltac:()] call might fail.   *)

Ltac chainToProp' xs :=
  lazymatch xs with
  | @eq_trans _ ?x ?y ?z ?p (@eq_trans _ ?x1 ?y1 ?z1 ?xs1 ?p1) =>
    let eq_ := chainToProp' (@eq_trans _ y y1 z1 xs1 p1) in
    constr:(@eq_trans _ x y z p eq_)
  | @eq_trans _ ?x ?y ?z ?p1 ?p2 =>
    constr:(@eq_trans _ x y z p1 p2)
  | _ => constr:(xs)
  end.

Ltac chainToProp xs :=
  let z := chainToProp' xs in exact z.

Notation "'calc' p" := (ltac:(chainToProp p)) (at level 70, right associativity, only parsing) : calc_scope.
Notation "a = b 'by' p ; pr" := (@eq_trans _ a b _ p pr) (at level 70, b at next level, right associativity, only parsing) : calc_scope.
Notation "a = b 'by' p 'end'" := (@eq_trans _ a b b p (@eq_refl _ b)) (b at next level, at level 70, only parsing): calc_scope.

(* Goal forall n : nat, True. *)
(*   intros n. *)
(*   assert (H : n+1 = 1+n). symmetry. rewrite plus_Sn_m. with (n:=0) (m:=n). *)

Open Scope calc_scope.
Require Import Arith.

(* Goal (forall (m n k : nat), n + m + k = k + n + m). *)
(*   intros m n k. *)
(*   set *)
(*   (@eq_trans nat (n + m + k) (k + (n + m)) (k + n + m) (Nat.add_comm (n + m) k) *)
(*   (@eq_trans nat (k + (n + m)) (k + n + m) (k + n + m) *)
(*              (Nat.add_assoc k n m) (@eq_refl nat (k + n + m)))) as blah. *)
(*   let z:=chainToProp' blah in apply z. *)
(*   set (ltac:(chainToProp  blah)) as zzz. *)

Definition ex_nat1 m n k : n + m + k = k + n + m :=
  calc (n + m) + k = k + (n + m) by Nat.add_comm _ _ ;
      _            = k + n + m  by Nat.add_assoc _ _ _
  end.

Set Printing Implicit.
Print ex_nat1.

(* Unset Printing Notations. *)

Set Printing Implicit.
Print ex_nat1.
Program Definition ex_nat_ring_fail (a b : nat) : (a + b) * (a + b) = a^2 + 2*a*b + b^2 :=
  calc (a + b) * (a + b)
       = a*a + b*a + a*b + b*b by ltac:(ring);
    _  = a*a + 2*a*b + b*b by _;
    _  = a^2 + 2*a*b + b^2 by ltac:(repeat rewrite Nat.pow_2_r;auto)
end.
