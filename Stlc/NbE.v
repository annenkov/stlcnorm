Require Import stlc.
Require Import stlc_bidir.

Reserved Notation "⟦ ty ⟧" (at level 50).
Reserved Notation "⟦ t ⟧ᵗ " (at level 50).

Open Scope type_scope.

(* Variables annotated with types  *)
Definition avar := var * Ty.

Fixpoint ty_sem (ty : Ty) :=
  match ty with
  | tInt => nat
  | tArr ty1 ty2 => ⟦ty1⟧ -> ⟦ty2⟧
  end
where "⟦ ty ⟧" := (ty_sem ty).

Definition sem_env := forall x : avar, ⟦snd x⟧.

Definition ty_eq_dec : forall ty1 ty2 : Ty, {ty1 = ty2} + {ty1 <> ty2}.
decide equality. Defined.

Definition transport {A : Type} {P : A -> Type} {a b : A} (p : a = b) : P a -> P b
  := fun a => match p with eq_refl => a end.

Notation "p # x"
  := (transport _ p x) (right associativity, at level 65).


Definition cast : forall ty1 ty2, ty_eqb ty1 ty2 = true -> forall (P : Ty -> Type), P ty1 -> P ty2.

Fixpoint term_sem (t : CExp) : := 


