(** * Interpreting STLC syntax into a cartesian-closed category *)
From Categories Require Import Category.Main Basic_Cons.CCC Notations.
Require Import List HList.

Import ListNotations.

(** A membership (proof-relevat) predicate (taken from Equations tutorial)*)
Reserved Notation " x ∈ s " (at level 70, s at level 10).

Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).
Hint Constructors In.


(** ** Basic definitions *)

Inductive Ty : Set :=
| tU : Ty
| tArr : Ty -> Ty -> Ty.

Notation "A :-> B" := (tArr A B) (at level 70).

Definition Ctx := list Ty.

Definition is_zero (n : nat) : bool :=
  match n with
  | O => true
  | _ => false
  end.

(** The intrincic syntax for STLC *)
Inductive Exp : Ctx -> Ty -> Type :=
| Star : forall {Γ}, Exp Γ tU
| Var : forall {Γ τ},
    τ ∈ Γ ->
    Exp Γ τ
| Lam : forall {Γ} (τ σ : Ty),
    Exp (τ :: Γ) σ ->
    Exp Γ (τ :-> σ)
| App : forall {Γ} (τ σ : Ty),
    Exp Γ (τ :-> σ) -> Exp Γ τ ->
    Exp Γ σ.

Reserved Notation "⟦ τ ⟧" (at level 5).

Open Scope object_scope.
Open Scope morphism_scope.

Fixpoint interpTy {C : Category} `{@CCC C} (τ : Ty) : C :=
    match τ with
    | tU => C.(CCC_term)
    | tArr τ1 τ2 => exponential (e:= CCC_HEXP _ _) ⟦τ1⟧ ⟦τ2⟧
    end
where "⟦ τ ⟧" := (interpTy τ).

(* Definition Env Γ := hlist Ty interpTy Γ. *)

Definition Env C := list C.

Equations get {A : Type} {a : A} (l : list A) (p : a ∈ l) : A:=
  get _ (here _) := a;
  get _ (there _ p') => get _ p'.

Reserved Notation "c⟦ Γ ⟧" (at level 6).
Fixpoint interpCtx {C : Category} `{@CCC C} (Γ : list Ty) : C :=
  match Γ with
  | nil => terminal (CCC_term _)
  | cons τ Δ => product c⟦Δ⟧ ⟦τ⟧ (CCC_HP _ _)
  end
where "c⟦ Γ ⟧" := (interpCtx Γ).


Equations varProj {C : Category} `{@CCC C} {τ : Ty} (Γ : list Ty) (m : τ ∈ Γ) : Hom c⟦Γ⟧ ⟦τ⟧ :=
  varProj _ (here _) := Pi_2;
  varProj Γ' (there _ m0) := compose Pi_1 (varProj _ m0).

Reserved Notation "e⟦ e ⟧" (at level 5).

Equations interpExp {Γ} {τ} {C : Category} `{@CCC C} (e : Exp Γ τ)
  : Hom c⟦Γ⟧ ⟦τ⟧ :=
 { e⟦ Star ⟧ := t_morph _ _; (* the unique morphism to the terminal object *)
   e⟦ Var v ⟧ := varProj _ v; (* projection from the context *)
   e⟦ Lam τ σ b ⟧ := Exp_morph_ex _ _ _ e⟦b⟧; (* the "curry" morphism (transpose) *)
   e⟦ App τ σ e1 e2 ⟧ :=
     (* the unique morphism to the product <e⟦e1⟧, e⟦e2⟧> *)
     let h := Prod_morph_ex (CCC_HP _ _) _ e⟦e1⟧ e⟦e2⟧
     (* eval ∘ <e⟦e1⟧, e⟦e2⟧>  *)
     in (eval _) ∘ h}
where "e⟦ e ⟧" := (interpExp e).