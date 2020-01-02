(** * An intrinsic Goedel's System T (STLC with natural numbers) *)

(** STLC part is basically a replay of test-suites and examples from the Equations plugin (some of them, in turn, based on Chlipala's CPDT) *)
(** We add a recursion over natural numbers and notations based on [Custom Entries] *)
From Equations Require Import Equations.
Require Import PeanoNat List.

Import ListNotations.

Import Nat.

Set Equations Transparent.

Reserved Notation " x ∈ s " (at level 70, s at level 10).

(** A membership (proof-relevat) predicate (taken from Equations tutorial)*)

Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).
Hint Constructors In.

(** ** Basic definitions *)

Inductive Ty : Set :=
| tU : Ty
| tNat : Ty
| tArr : Ty -> Ty -> Ty.

Notation "A :-> B" := (tArr A B) (at level 70).

Definition Ctx := list Ty.

Definition is_zero (n : nat) : bool :=
  match n with
  | O => true
  | _ => false
  end.

(** The intrincic syntax for STLC *)
Inductive Exp : Ctx -> Ty -> Set :=
| Star : forall {Γ}, Exp Γ tU
| Var : forall {Γ τ},
    τ ∈ Γ ->
    Exp Γ τ
| Lam : forall {Γ} (τ σ : Ty),
    Exp (τ :: Γ) σ ->
    Exp Γ (τ :-> σ)
| App : forall {Γ} (τ σ : Ty),
    Exp Γ (τ :-> σ) -> Exp Γ τ ->
    Exp Γ σ
| Zero : forall {Γ}, Exp Γ tNat
| Suc : forall {Γ}, Exp Γ (tNat :-> tNat)
| Nat_elim : forall {Γ τ}, Exp Γ τ -> Exp Γ (tNat :-> (τ :-> τ)) -> Exp Γ (tNat :-> τ).

(** Let's create custom notations for our lambda terms *)

Declare Custom Entry ty.
Declare Custom Entry lambda.

Notation "[\ e \]" := e (e custom ty at level 2).
Notation "'*'" := tU (in custom ty).
Notation "'ℕ'" := tNat (in custom ty at level 1).
Notation "'SUC'" := Suc (in custom lambda at level 1).
Notation " A -> B" := (tArr A B) (in custom ty at level 4, right associativity,
                                    A custom ty,
                                    B custom ty at level 4).
Notation "( x )" := x (in custom ty, x at level 2).

Notation "[! e !]" := e (e custom lambda at level 2).
Notation "()" := (Star) (in custom lambda).
Notation "'v0'" := (Var (here _)) (in custom lambda).
Notation "'v1'" := (Var (there _ (here _))) (in custom lambda).
Notation "'v2'" := (Var (there _ (there _ (here _)))) (in custom lambda).
Notation " 'λ' e : τ -> σ" := (Lam τ σ e) (in custom lambda at level 1,
                                              e custom lambda at level 2,
                                              τ custom ty at level 2,
                                              σ custom ty at level 2).
Notation " 'λ' e " := (Lam _ _ e) (in custom lambda at level 1,
                                             e custom lambda at level 2).

Notation " 'ℕ_elim' ( e0 , es ) " := (Nat_elim e0 es)
                                       (in custom lambda at level 1,
                                           e0 custom lambda,
                                           es custom lambda).

Notation "e1  e2" := (App _ _ e1 e2) (in custom lambda at level 1,
                                                e1 custom lambda,
                                                e2 custom lambda at level 2
                                                (* , *)
                                                (* τ custom ty at level 2, *)
                                                (* σ custom ty at level 2 *)
                                            ).
Notation "( x )" := x (in custom lambda, x at level 2).
Notation "{ x }" := x (in custom lambda, x constr).

Definition unit_arrow2 := [\ * -> * -> * \].

Definition id_unit : Exp [] (tU :-> tU) :=
  [! λ v0 : * -> * !].

Definition id_unit_unit : Exp [] (tU :-> (tU :-> tU)) :=
  [! λ λ v0 !].

Definition id_fun_unit : Exp [] ((tU :-> tU) :-> (tU :-> tU)) :=
  [! λ v0 !].

Definition id_unit_app : Exp [] (tU :-> tU) :=
  [! {id_fun_unit} (λ v0) !].


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

Derive NoConfusion for nat.
Derive NoConfusion for Ty.

Reserved Notation "⟦ τ ⟧" (at level 50).

Definition nat_elim : forall A : Type, A -> (nat -> A -> A) -> nat -> A :=
  fun A => nat_rect (fun _ => A).

Equations denoteTy (τ : Ty) : Set :=
  { ⟦ tU ⟧ := unit;
    ⟦ tNat ⟧ := nat;
    ⟦ tArr τ1 τ2 ⟧ := ⟦ τ1 ⟧ -> ⟦ τ2 ⟧ }

where "⟦ τ ⟧" := (denoteTy τ).

Notation "ρ ,, x" := (HCons x ρ) (at level 50).

Reserved Notation "⟦ e ⟧ ρ" (at level 50).

Definition Env Γ := hlist Ty denoteTy Γ.

Equations denoteExp {Γ τ} (ρ : Env Γ) (e : Exp Γ τ) : ⟦τ⟧ :=
  { ⟦ Star ⟧ρ := tt;
    ⟦ Var i ⟧ρ  := hget ρ i;
    ⟦ Lam τ σ e ⟧ρ := fun (x : ⟦τ⟧) => denoteExp (ρ ,, x) e;
    ⟦ App τ σ e1 e2 ⟧ρ := (⟦e1⟧ρ) (⟦e2⟧ρ);
    ⟦ Zero ⟧ρ := O;
    ⟦ Suc ⟧ρ := S;
    ⟦ Nat_elim e0 f⟧ρ := fun n => nat_elim _ (⟦e0⟧ρ) (⟦f⟧ρ) n }

where "⟦ e ⟧ ρ" := (denoteExp ρ e).

Definition idf := ⟦ id_unit ⟧HNil.

Definition my_add_syn : Exp [] (tNat :-> (tNat :-> tNat)) :=
  [! λ λ (ℕ_elim(v0, (λ λ (SUC v0))) v1) !].

Definition my_add := Eval compute in ⟦my_add_syn⟧HNil.

Compute my_add 1 2.

Lemma my_add_add n m :
  my_add n m = n + m.
Proof.
  induction n;simpl;auto.
Qed.