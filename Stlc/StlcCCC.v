(** * Interpreting STLC syntax into a cartesian-closed category *)

(** The interpretation is fairly standard (see e.g. Andrew Pitts. "Brief Notes on the Category Theoretic Semantics of Simply Typed Lambda Calculus" for a concise introduction), but ways of representing syntax might vary. The way we encode intrinsic syntax and syntactic substitutions comes from an approach commonly used in Agda (see, e.g. Programming Language Foundations in Agda. Part 2. DeBruijn. https://plfa.github.io/DeBruijn/) *)

From Categories Require Import Category.Main Basic_Cons.CCC
     Basic_Cons.Product Notations.
From Equations Require Import Equations.
Require Import List HList.
Require Import CalcNotations CalcNotationsTactic.

Import ListNotations.

(** We allow definitions produced by the Equations plugin to be transparent, i.e. we can compute with them *)
Set Equations Transparent.

Definition cprod {C : Category} {HP : @Has_Products C} (A B : C) : Product A B := HP A B.

Notation "⟨ f ; g ⟩" := (@Prod_morph_ex _ _ _ (cprod _ _) _ f g) (at level 50): morphism_scope.

(** A (proof-relevant) membership predicate (taken from the Equations tutorial) *)
Reserved Notation " x ∈ s " (at level 70, s at level 10).

Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
where " x ∈ s " := (In x s).

Arguments here {_ _ _}.
Arguments there {_ _ _ _}.
Hint Constructors In.
Derive Signature NoConfusion for In.
Derive NoConfusion for list.


(** ** The intrinsic syntax for STLC *)

(** Types *)
Inductive Ty : Set :=
| tU : Ty
| tArr : Ty -> Ty -> Ty.
Derive NoConfusion for Ty.

Notation "A :-> B" := (tArr A B) (at level 70, right associativity).

(** Contexts are list of types *)
Definition Ctx := list Ty.

Notation "⋄" := (nil : list Ty).
Notation "Γ , τ" := (τ :: Γ : list Ty) (at level 10) : ctx_scope.
Notation "Γ ,, Γ'" := (Γ' ++ Γ : list Ty) (at level 10) : ctx_scope.


(** Intrinsically-typed lambda terms *)

Open Scope ctx_scope.
Inductive Exp : Ctx -> Ty -> Type :=
| Star : forall {Γ}, Exp Γ tU

| Var : forall {Γ τ},

    τ ∈ Γ ->
(* ---------- *)
    Exp Γ τ

| Lam : forall {Γ} {τ σ : Ty},

    Exp (Γ,τ) σ ->
(* ------------------- *)
    Exp Γ (τ :-> σ)

| App : forall {Γ} {τ σ : Ty},

    Exp Γ (τ :-> σ) -> Exp Γ τ ->
(* ----------------------------- *)
    Exp Γ σ.

Derive Signature for Exp.
Derive NoConfusion for Exp.

Declare Custom Entry ty.
Declare Custom Entry lambda.

Notation "` n"  := (Var n) (at level 10) : exp_scope.
Notation "'v0'" := (Var here) : exp_scope.
Notation "'v1'" := (Var (there here)) : exp_scope.
Notation "'v2'" := (Var (there (there here))) : exp_scope.
Notation " 'λ' e " := (Lam e) (at level 10) : exp_scope.
Notation "e1 ⋅ e2" := (App e1 e2) (at level 10) : exp_scope.

Reserved Notation "⟦ τ ⟧" (at level 5).

(** Some extra lemmas about product morphisms which will be useful later *)

Open Scope morphism_scope.


(** We use the "calculational proof" style for the lemma below using the tactic notation allowing for chaining intermediate results in the equational reasoning. *)
Lemma Prod_morph_distr_r {C : Category} `{@CCC C} {A X Y Z  : C}
      {f : A –≻ X} {g : A –≻ Y} {h :  Z –≻ A} :
  ⟨ f ; g ⟩ ∘ h = ⟨ f ∘ h ; g ∘ h ⟩.
Proof.
  apply Prod_morph_unique with (r1:= f ∘ h) (r2:=g ∘ h).
  - calc
      (Pi_1 ∘ ⟨ f; g ⟩ ∘ h) = ((Pi_1 ∘ ⟨ f; g ⟩) ∘ h) by now rewrite <-assoc.
                       _  = (f ∘ h) by now rewrite Prod_morph_com_1
    end.
  - calc
      (Pi_1 ∘ ⟨ f; g ⟩ ∘ h) = ((Pi_2 ∘ ⟨ f; g ⟩) ∘ h) by now rewrite <-assoc.
                       _  = (g ∘ h) by now rewrite Prod_morph_com_2
    end.
  - apply Prod_morph_com_1.
  - apply Prod_morph_com_2.
Qed.

Lemma Exp_morph_com' (C : Category) `{@CCC C}
      (c d : C) (z : C)
      (f : Hom (product z c (cprod z c)) d) :
  f = eval _ ∘ ⟨ (@curry C _ CCC_HEXP _ _ _ f) ∘ Pi_1 ; Pi_2 ⟩.
Proof.
  specialize (Exp_morph_com (CCC_HEXP _ _) _ f) as H1.
  simpl in H1. rewrite id_unit_left in H1.
  exact H1.
Qed.

Open Scope calc_scope.

(** A simple notation allowing to build a term using rewrites in non-interactive mode. It tries to rewrite both left-to-right and right-to-left completing the proof by reflexivity. *)
Notation "{{ f }}" := (ltac:((rewrite f;reflexivity) || (rewrite <-f; reflexivity)|| fail "Could not rewrite with" f)) (at level 70) : calc_scope.

(** We use the "calculational proof" style again, but this time the notation is defined at the term level and not at the tactic level. It allows for the proof style similar to Lean and Agda. The curly braces {{ }} mean that the witness of a step is built by applying the [rewrite] tactic with the given lemma *)
Definition Prod_morph_decompose {C : Category} `{@CCC C} {A X Y : C}
      (f : A –≻ X) (g : A –≻ Y) :
  ⟨ f ∘ Pi_1; Pi_2 ⟩ ∘ ⟨ id ; g ⟩ = ⟨ f; g ⟩ :=
  calc
    ⟨ f ∘ Pi_1; Pi_2 ⟩ ∘ ⟨ id ; g ⟩ =  ⟨ (f ∘ Pi_1) ∘ ⟨ id ; g ⟩ ; Pi_2  ∘ ⟨ id ; g ⟩ ⟩
                                       by Prod_morph_distr_r ;
                              _   =  ⟨ f ∘ (Pi_1 ∘ ⟨ id ; g ⟩) ; Pi_2  ∘ ⟨ id ; g ⟩ ⟩
                                       by {{ @assoc }} ;
                              _   =  ⟨ f ∘ id; Pi_2  ∘ ⟨ id ; g ⟩ ⟩
                                       by {{ @Prod_morph_com_1 }} ;
                              _   =  ⟨ f ∘ id; g ⟩
                                       by {{ @Prod_morph_com_2 }} ;
                              _   =  ⟨ f; g ⟩ by {{ id_unit_right }}
  end.

(** ** Interpreting syntax *)
Open Scope object_scope.
Open Scope morphism_scope.

Fixpoint interpTy {C : Category} `{@CCC C} (τ : Ty) : C :=
    match τ with
    | tU => C.(CCC_term)
    | τ1 :-> τ2 => exponential (e:= CCC_HEXP _ _) ⟦τ1⟧ ⟦τ2⟧
    end
where "⟦ τ ⟧" := (interpTy τ).

Definition Env C := list C.

Equations get {A : Type} {a : A} (l : list A) (p : a ∈ l) : A:=
  get _ here := a;
  get _ (there p') => get _ p'.

Reserved Notation "c⟦ Γ ⟧" (at level 6).

Fixpoint interpCtx {C : Category} `{@CCC C} (Γ : Ctx) : C :=
  match Γ with
  | nil => terminal (CCC_term _)
  | cons τ Δ => product c⟦Δ⟧ ⟦τ⟧ (CCC_HP c⟦Δ⟧ ⟦τ⟧)
  end
where "c⟦ Γ ⟧" := (interpCtx Γ).

Equations varProj {C : Category} `{@CCC C} {τ : Ty} (Γ : Ctx) (m : τ ∈ Γ) : Hom c⟦Γ⟧ ⟦τ⟧ :=
  varProj _ here := Pi_2;
  varProj Γ' (there m0) := compose Pi_1 (varProj _ m0).

Reserved Notation "e⟦ e ⟧" (at level 5).

Open Scope exp_scope.

Equations interpExp {Γ} {τ} {C : Category} `{@CCC C} (e : Exp Γ τ)
  : Hom c⟦Γ⟧ ⟦τ⟧ :=
 { e⟦ Star ⟧ := t_morph _ _; (* the unique morphism to the terminal object *)
   e⟦ `v ⟧ := varProj _ v; (* projection from the context *)
   e⟦ λ b ⟧ := curry _ e⟦b⟧;
   e⟦ e1 ⋅ e2 ⟧ := (eval _) ∘ ⟨ e⟦e1⟧; e⟦e2⟧ ⟩ }
where "e⟦ e ⟧" := (interpExp e).

Module Examples.

  Example interp_id {C : Category} `{@CCC C} :
    e⟦λ v0 : Exp nil (tU :-> tU) ⟧ =
    (curry _ Pi_2 : CCC_term –≻ CCC_HEXP _ CCC_term CCC_term).
  Proof. reflexivity. Qed.

End Examples.


(** ** Interpreting substitutions  *)

Reserved Notation "Γ ==> Δ" (at level 5).

Open Scope ctx_scope.

Inductive ctx_morph Γ : Ctx -> Type :=
| s_empty : Γ ==> ⋄
| s_ext : forall {Δ τ}, Γ ==> Δ -> Exp Γ τ ->
                   Γ ==> (Δ,τ)
where "Γ ==> Δ " := (ctx_morph Γ Δ).

Inductive rename_morph (Γ : Ctx): Ctx -> Type :=
| r_empty : rename_morph Γ []
| r_cons : forall τ Δ,
    τ ∈ Γ -> rename_morph Γ Δ ->
    rename_morph Γ (Δ,τ).

Arguments r_empty {_}.
Arguments r_cons {_ _ _}.


Equations wkn_ren {Γ Δ τ}: rename_morph Γ Δ -> rename_morph (Γ,τ) Δ :=
  wkn_ren r_empty := r_empty ;
  wkn_ren (r_cons n r) := r_cons (there n) (wkn_ren r).

Equations ext_ren {Γ Δ τ}: rename_morph Γ Δ -> rename_morph (Γ,τ) (Δ,τ) :=
  ext_ren r_empty := r_cons here r_empty ;
  ext_ren (r_cons n r) := r_cons here (r_cons (there n) (wkn_ren r)).

Equations id_ren {Γ}: rename_morph Γ Γ :=
  @id_ren nil := r_empty;
  @id_ren (σ :: Γ') := r_cons here (wkn_ren id_ren).

Equations renF {Γ Δ} : rename_morph Γ Δ -> (forall τ, τ ∈ Δ -> τ ∈ Γ) :=
  renF (r_cons n r) τ here := n;
  renF (r_cons n r) τ (there n) := renF r τ n.

Reserved Notation "t .[ τ ]" (at level 20).

Reserved Notation "r⟦ σ ⟧" (at level 5).
Reserved Notation "s⟦ σ ⟧" (at level 5).


Equations interpRen {C : Category} `{@CCC C} {Γ Δ} (r : rename_morph Γ Δ) : Hom c⟦Γ⟧ c⟦Δ⟧ :=
  { r⟦ r_empty ⟧ := t_morph _ _;
    r⟦ r_cons n r⟧ := ⟨ r⟦r⟧ ; varProj _ n ⟩ }

where "r⟦ r ⟧" := (interpRen r).

Equations interpSubst {C : Category} `{@CCC C} {Γ Δ} (σ : Γ ==> Δ) : Hom c⟦Γ⟧ c⟦Δ⟧ :=
  { s⟦ s_empty ⟧ := t_morph _  c⟦Γ⟧ ;
    s⟦ s_ext _ s t ⟧ := ⟨ s⟦s⟧ ; e⟦t⟧ ⟩ }

where "s⟦ σ ⟧" := (interpSubst σ).


Definition idMap {Γ : Ctx} : forall τ, τ ∈ Γ -> τ ∈ Γ := fun _ n => n.

Equations ext {Γ Δ : Ctx} :
   (forall {τ}, τ ∈ Γ -> τ ∈ Δ) ->
(* ------------------------------------ *)
   (forall σ τ, τ ∈ Γ,σ -> τ ∈ Δ,σ ) :=

  ext f _ _ here := here ;
  ext f _ _ (there n) := there (f _ n).


Equations rename {Γ Δ : Ctx} {τ} :
  (forall {τ}, τ ∈ Γ -> τ ∈ Δ) ->
(* ----------------------------- *)
  (Exp Γ τ -> Exp Δ τ) :=

  rename f Star := Star ;
  rename f (Var n) := Var (f _ n);
  rename f (Lam b) := Lam (rename (ext f _)  b) ;
  rename f (App e1 e2) := App (rename f e1) (rename f e2).

Import FunctionalExtensionality.

Lemma idMap_rename {Γ : Ctx} {τ} (e : Exp Γ τ):
  rename idMap e = e.
Proof.
  induction e;auto.
  - simpl.
    assert (ext (Δ:=Γ) idMap τ = idMap).
    { apply functional_extensionality_dep. intro σ0.
      apply functional_extensionality_dep.
      intros n. funelim (ext _ _ _ _);auto.  }
    rewrite H. rewrite IHe. reflexivity.
  - simpl. congruence.
Qed.

Lemma there_renF : ∀ (Γ : Ctx) (xs0 : list Ty) (r : rename_morph Γ xs0)
                     (τ σ: Ty) (i : τ ∈ xs0),
    there (y:=σ) (renF r τ i) = renF (wkn_ren r) τ i.
Proof.
  intros Γ Δ r τ σ n.
  funelim (renF r τ n);auto.
  simp wkn_ren.
Qed.


Lemma ext_ext_ren {Γ Δ τ} (r : rename_morph Γ Δ) :
  ext (renF r) τ = renF (ext_ren r).
Proof.
  apply functional_extensionality_dep. intros σ.
  apply functional_extensionality_dep. intros n.
  funelim (ext _ _ _ _).
  - simp ext. destruct r;auto.
  - simp ext. funelim (renF _ _ _);auto.
    simp ext_ren. simp renF.
    apply there_renF.
Qed.

Lemma wkn_ren_interp {C : Category} `{@CCC C} {Γ Δ} {τ : Ty}
  (r : rename_morph Γ Δ) :
  r⟦wkn_ren (τ:=τ) r⟧ = r⟦r⟧ ∘ Pi_1.
Proof.
  funelim (wkn_ren r).
  - apply t_morph_unique.
  - simpl. rewrite H. symmetry. apply Prod_morph_distr_r.
Qed.

Lemma varProj_renF:
      ∀ (C : Category) (H : CCC C) (Γ : list Ty)
        (τ : Ty) (i : τ ∈ Γ) (Δ : Ctx) (f : rename_morph Δ Γ),
        varProj Δ (renF f τ i) = varProj Γ i ∘ r⟦ f ⟧.
Proof.
  intros C H Γ τ i Δ f.
  funelim (renF _ _ _).
  - simp renF. simp varProj. simp interpRen.
    symmetry. apply Prod_morph_com_2.
  - simp renF. simp varProj. simp interpRen.
    rewrite H by reflexivity.
    rewrite assoc. refine (f_equal2 _ _ eq_refl).
    symmetry. apply Prod_morph_com_1.
Qed.


Lemma rename_interp {C : Category} `{@CCC C} {Γ Δ} {τ : Ty}
         {f : rename_morph Δ Γ}
         (e : Exp Γ τ) :
  e⟦rename (renF f) e⟧ = e⟦e⟧ ∘ r⟦f⟧.
Proof.
  revert dependent Δ.
  induction e;fold interpTy;intros.
  - apply t_morph_unique.
  - apply varProj_renF.
  - simpl. specialize (IHe (Δ,τ)).
    rewrite ext_ext_ren. rewrite IHe.
    rewrite curry_compose. repeat f_equal.
    funelim (ext_ren f). simpl. apply f_equal2.
    apply t_morph_unique.
    reflexivity.
    simpl. apply f_equal2;auto.
    rewrite wkn_ren_interp.
    symmetry. apply Prod_morph_distr_r.
  - simpl. fold interpTy. rewrite assoc. apply f_equal2.
    rewrite IHe1. rewrite IHe2.
    symmetry. apply Prod_morph_distr_r. reflexivity.
Qed.

Lemma id_ren_id_morph {C : Category} `{@CCC C} {Γ} :
  r⟦id_ren (Γ:=Γ)⟧ = Category.id.
Proof.
  induction Γ;simpl.
  - apply t_morph_unique.
  - rewrite wkn_ren_interp. rewrite IHΓ.
    rewrite id_unit_left.
    apply (Prod_morph_unique _ _ Pi_1 Pi_2).
    + apply Prod_morph_com_1.
    + apply Prod_morph_com_2.
    + apply id_unit_right.
    + apply id_unit_right.
Qed.


(** Since context morphisms are "lists" of well-typed expressions, we "map" a weakening renaming (which is basically [+1] for de Bruijn indices) over the "list" to get a "weakened" context morphism [Γ,τ ==> Δ], s.t. expressions in Δ are well-typed in the extended context [Γ,τ] *)
Equations wkn {Γ Δ τ} : Γ ==> Δ -> (Γ,τ) ==> Δ :=
  wkn (s_empty _) := (s_empty _);
  wkn (s_ext _ f e) := s_ext _ (wkn f) (rename (renF (wkn_ren id_ren)) e) .

Lemma wkn_interp {C : Category} `{@CCC C} {Γ Δ} (s : Γ ==> Δ) (τ : Ty) :
  s⟦ wkn (τ:=τ) s ⟧ = s⟦s⟧ ∘ Pi_1.
Proof.
  funelim (wkn s).
  - apply t_morph_unique.
  - simpl. rewrite H by reflexivity.
    erewrite (rename_interp (τ:=τ0)). rewrite wkn_ren_interp.
    rewrite id_ren_id_morph. rewrite id_unit_left.
    symmetry. apply Prod_morph_distr_r.
Qed.


(** Using the previously defined machinery we can now define the identity context morhism *)
Equations idS Γ : Γ ==> Γ :=
  idS nil := s_empty _ ;
  idS (e :: Γ') := s_ext _ (wkn (idS Γ')) (Var here).

Lemma idS_id_morph {C : Category} `{@CCC C} {Γ} :
  s⟦idS Γ⟧ = Category.id.
Proof.
  induction Γ;simpl.
  - apply t_morph_unique.
  - rewrite wkn_interp. rewrite IHΓ.
    rewrite id_unit_left.
    apply (Prod_morph_unique _ _ Pi_1 Pi_2).
    + apply Prod_morph_com_1.
    + apply Prod_morph_com_2.
    + apply id_unit_right.
    + apply id_unit_right.
Qed.


(** Given a context morphism, returns a function mapping variables in Γ to terms well-typed in Δ *)
Equations substF {Γ Δ} : Δ ==> Γ -> forall τ, τ ∈ Γ -> Exp Δ τ :=
  substF (s_ext _ t) _ here := t ;
  substF (@s_ext _ _ _ s t) _ (there n) := substF s _ n.

Definition extsS {Γ Δ σ} :
  (Γ ==> Δ) ->
(*-------------------------------*)
  (Γ,σ) ==> (Δ,σ)

  := fun s => s_ext _ (wkn s) (Var here).


Equations subst {Γ Δ} :
  Δ ==> Γ ->
(*-------------------------------*)
  (forall τ, Exp Γ τ -> Exp Δ τ) :=

  subst s _ Star := Star ;
  subst s _ (Var n) := (substF s) _ n ;
  subst s _ (Lam b) := Lam (subst (extsS s) _ b) ;
  subst s _ (App e1 e2) => App (subst s _ e1) (subst s _ e2).

Arguments Prod_morph_unique {_ _ _ _ _} _ _ {_ _}.
Arguments Prod_morph_com_1 {_ _ _ _ _}.
Arguments Prod_morph_com_2 {_ _ _ _ _}.

Lemma varProj_commutes {C : Category} `{@CCC C} {Γ Δ : Ctx} {τ} n (s : Γ ==> Δ)
  : varProj Δ n ∘ s⟦ s ⟧ = e⟦ substF s τ n ⟧.
Proof.
  funelim (substF s τ n).
  + rewrite substF_equation_2. simpl.
    rewrite Prod_morph_com_2. reflexivity.
  + rewrite substF_equation_3. simpl.
    rewrite <- H by reflexivity.
    rewrite assoc.
    rewrite Prod_morph_com_1. reflexivity.
Qed.

Lemma subst_semantics {C : Category} `{@CCC C} {Γ Δ τ}
       (s : Γ ==> Δ) (t : Exp Δ τ) :
  e⟦ subst s _ t ⟧ = e⟦t⟧ ∘ s⟦s⟧.
Proof.
  revert s.
  revert dependent Γ.
  induction t;intros Γ' s.
  - apply t_morph_unique.
  - symmetry. apply varProj_commutes.
  - simpl. rewrite IHt. simpl.
    rewrite wkn_interp.
    symmetry. apply curry_compose.
  - simpl. fold interpTy.
    rewrite assoc.
    rewrite IHt1.
    rewrite IHt2.
    apply f_equal2;auto.
    symmetry. apply Prod_morph_distr_r.
Qed.

Definition munit : [tU;tU] ==> [tU;tU].
  constructor. constructor. apply s_empty.
  constructor. constructor. Defined.

Definition singleSubstMorph {Γ τ} : Exp Γ τ -> Γ ==> (Γ,τ) :=
  fun e => s_ext _ (idS Γ) e.

Definition singleSubst {Γ τ σ} :

  Exp (Γ,σ) τ -> Exp Γ σ ->
(*--------------------------*)
  Exp Γ τ

  := fun e1 e2 => subst (singleSubstMorph e2) _ e1.

Notation "e1 .[ e2 ]" := (singleSubst e1 e2) (at level 20).

Lemma single_subst_semantics {C : Category} `{@CCC C} {Γ τ σ}
       (e1 : Exp (Γ,τ) σ)(e2 : Exp Γ τ) :
  e⟦e1.[e2]⟧ = e⟦e1⟧ ∘ ⟨id ; e⟦e2⟧ ⟩.
Proof.
  refine
    (calc e⟦e1.[e2]⟧ = e⟦e1⟧ ∘ ⟨s⟦idS _⟧ ; e⟦e2⟧ ⟩ by subst_semantics _ _;
                  _  = e⟦e1⟧ ∘ ⟨id ; e⟦e2⟧ ⟩ by {{ @idS_id_morph }}
          end ).
Qed.

(** Examples of how we can use the notation and apply substitutions *)

Definition id_unit_syn : Exp nil (tU :-> tU) :=
  λ v0.

Definition ex_syn : Exp [tU;tU :-> tU] (tU :-> tU) :=
  λ (v2 ⋅ v1).

Example ex_syn_subst : ex_syn.[Star] = λ (v1 ⋅ Star).
Proof. reflexivity. Qed.


(** ** Interpreting equations  *)

Reserved Notation "e1 ≡β e2" (at level 22).

(** We define β-equal terms using the following inductive relation *)
Inductive StlcEq : forall {Γ : Ctx} {τ : Ty}, Exp Γ τ -> Exp Γ τ -> Type :=
| seq_refl : forall {Γ τ} (e : Exp Γ τ),

    e ≡β e

| seq_sym : forall {Γ τ} (e1 : Exp Γ τ) (e2 : Exp Γ τ),

    e1 ≡β e2 ->
 (* ---------  *)
    e2 ≡β e1

| seq_beta : forall {Γ τ σ} (e1 : Exp (Γ,τ) σ) (e2 : Exp Γ τ),

    (λ e1) ⋅ e2 ≡β e1.[e2]

| seq_app_cong_eq : forall {Γ τ σ} (e1 e1' : Exp Γ (τ :-> σ)) (e2 e2' : Exp Γ τ),

    e1 ≡β e1'  ->  e2 ≡β e2' ->
 (* ---------------------------- *)
    (e1 ⋅ e2) ≡β (e1' ⋅ e2')

where "e1 ≡β e2" := (StlcEq e1 e2).

Arguments eval {_ _ _ _ _}.
Arguments curry {_ _ _ _ _ _}.

(** Interpreting the intrinsically-typed β-equality also shows soundness *)
Equations interpEq {C : Category} `{@CCC C} {Γ τ} {e1 e2 : Exp Γ τ} :
  e1 ≡β e2 -> e⟦e1⟧ = e⟦e2⟧ :=

  interpEq (seq_refl e) := eq_refl;
  interpEq (seq_sym e1 e2 eq1) := eq_sym (interpEq eq1);
  interpEq (seq_app_cong_eq e1 e1' e2 e2' eq1 eq2) :=
       f_equal2 _ (f_equal2 _ (interpEq eq1) (interpEq eq2)) eq_refl;
  interpEq (seq_beta (Γ:=Γ) (τ:=τ) (σ:=σ) e1 e2) :=
    calc
      eval ∘ ⟨ curry e⟦ e1 ⟧; e⟦ e2 ⟧ ⟩
        = eval ∘ ⟨ curry e⟦ e1 ⟧ ∘ Pi_1; Pi_2 ⟩ ∘ ⟨ id ; e⟦ e2 ⟧ ⟩ by {{ @Prod_morph_decompose }};
      _ = (eval ∘ ⟨ curry e⟦ e1 ⟧ ∘ Pi_1; Pi_2 ⟩) ∘ ⟨ id ; e⟦ e2 ⟧ ⟩ by {{ @assoc }} ;
      _ = e⟦ e1 ⟧ ∘ ⟨ id; e⟦ e2 ⟧ ⟩ by  {{ Exp_morph_com' }} ;
      _ = e⟦ e1 .[ e2] ⟧ by {{ @single_subst_semantics }}
   end.
