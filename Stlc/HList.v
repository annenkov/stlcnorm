From Equations Require Import Equations.

Set Equations Transparent.

Reserved Notation " x ∈ s " (at level 70, s at level 10).

(** A membership (proof-relevat) predicate (taken from Equations tutorial)*)

Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).
Hint Constructors In.

(** Taken from Adam Chlipala's CPDT (Equations implements this in the test-suite) *)
Section hlist.
  Variable A : Type.
  Variable B : A -> Type.
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).
End hlist.

Arguments HNil {A B}.
Arguments HCons {A B x ls}.

Equations hget {A B x} {xs : list A} (hxs : hlist A B xs) (i : x ∈ xs) : B x :=
  hget (HCons hx hxs') (here _) := hx;
  hget (HCons hx hxs') (there _ _) := hget hxs' _.
