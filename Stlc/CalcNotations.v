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
