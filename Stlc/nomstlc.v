Require Import PeanoNat Peano_dec.
Require Import ProofIrrelevance.
Require Import CustomTactics.

Require Import Nom.
Require Import OrdSet.

Module TSetMod := SetExt PeanoNat.Nat.

Module AtomN <: Atom.
  Module V := TSetMod.
  Axiom Atom_inf : forall (X : V.t), {x : V.elt | ~ V.In x X}.
  Definition eq_dec := Nat.eq_dec.
End AtomN.

Module NomN := Nominal AtomN.

Import NomN.
Import NomN.Atom.V.
Import NomAtom.
Import PFin.


Notation Atom := NomN.Atom.V.elt.

(** ** Basic definitions *)

Inductive Ty : Set :=
  | tInt : Ty
  | tArr : Ty -> Ty -> Ty.

Instance NomTy : NomSet.
    refine (
        {| Carrier := Ty;
           action := fun p ty => ty;
           supp := fun ty => empty;
           action_id := fun a => eq_refl _;
           action_compose := fun a p1 p2 => eq_refl;
           support_spec := fun p ty H => eq_refl
        |}).
Defined.

Notation "A :-> B" := (tArr A B) (at level 70).

(** The syntax for STLC. We use [Atom] type to represent variable names *)
Inductive Exp : Type :=
  | Int (n : nat)
  | Var (a : Atom)
  | Lam (a : Atom) (e : Exp)
  | App (e1 : Exp) (e2 : Exp).

(** Action of a permutation [p] on epressions [Exp] *)
Fixpoint ac_exp (p : Perm) (e : Exp) : Exp :=
  match e with
  | Int n => Int n
  | Var v => Var ((perm p) v)
  | Lam v e1 => Lam ((perm p) v) (ac_exp p e1)
  | App e1 e2 => App (ac_exp p e1) (ac_exp p e2)
  end.

(** Support of an epression [e] is a set of all atoms *)
Fixpoint supp_exp (e : Exp) : Atom.V.t :=
  match e with
  | Int n => empty
  | Var v => singleton v
  | Lam v e1 => union (singleton v) (supp_exp e1)
  | App e1 e2 => union (supp_exp e1) (supp_exp e2)
  end.

(** Set of free variables *)
Fixpoint fv_exp (e : Exp) : PFin  :=
  match e with
  | Int n => empty
  | Var v => singleton v
  | Lam v e1 => diff (fv_exp e1) (singleton v)
  | App e1 e2 => union (fv_exp e1) (fv_exp e2)
  end.

(** Set of all variables is the support of [e] *)
Definition vars_exp (e : Exp) : PFin  := supp_exp e.


(** Nominal set of lambda expressions *)
Instance NomExp : NomSet.
  refine (
        {| Carrier := Exp;
           action := fun p e => ac_exp p e;
           supp := fun e => supp_exp e;
           action_id := fun e => _;
           action_compose := fun e p1 p2 => _;
           support_spec := _
        |}).
- induction e;auto.
  + simpl. rewrite IHe. reflexivity.
  + simpl. rewrite IHe1. rewrite IHe2. reflexivity.
- induction e;auto.
  + simpl. rewrite IHe. reflexivity.
  + simpl. rewrite IHe1. rewrite IHe2. reflexivity.
- intros p e H. induction e.
  + reflexivity.
  + simpl. rewrite H;auto with set.
  + simpl. rewrite H;simpl;auto with set.
    rewrite IHe;auto.
    intros a0 Ha. apply H. simpl;auto with set.
  + simpl.
    assert (He1 : forall a, In a (supp_exp e1) -> perm p a = a) by
        (intros;apply H;simpl;auto with set).
    assert (He2 : forall a, In a (supp_exp e2) -> perm p a = a) by
        (intros;apply H;simpl;auto with set).    
    rewrite IHe1;auto.
    rewrite IHe2;auto.
Defined.

Notation "a ∪ b" := (union a b) (at level 50).
Import SetFacts.


(** ** Alpha-equivalence *)

(** We introduce the following notation [a ## (a1,a2,...,an)] 
    denotiong that the atom [a] is fresh for all the elements in the n-tuple.
    That is, [ (a # a1) /\ (a # a2) ... /\ (a # an)] *)
Notation "a ## '(' a1 , .. , an ')'" :=
  ((and (fresh a a1)) .. (and (fresh a an) True) ..) (at level 40).
Reserved Notation "e1 =α e2" (at level 80).

Inductive ae_exp : NomExp -> NomExp -> Prop :=
| ae_int : forall n,
    (Int n) =α (Int n)
| ae_var : forall (a : NomAtom),
    (Var a) =α (Var a)
| ae_lam : forall (a b : NomAtom) (e1 e2 : NomExp) (vs : PFin),
    (* this is equivalent to explicitly specifying [c ## (a, b, vars_exp e1, vars_exp e2])
    see "Alpha-Structural Induction and Recursion for the Lambda Calculus in Constructive Type Theory"*)
    (forall (c : NomAtom), c # vs ->
    ((swap a c) @ e1) =α ((swap b c) @ e2)) ->
    (Lam a e1) =α (Lam b e2)
| ae_app : forall e1 e2 e1' e2',
    e1 =α e1' ->
    e2 =α e2' ->
    (App e1 e2) =α (App e1' e2')
where "e1 =α e2" := (ae_exp e1 e2).

Definition get_fresh (a : PFin) : { b : NomAtom | b # a}.
  pose (Atom.Atom_inf (supp a)) as c.
  destruct c. exists x. unfold fresh. now apply disjoint_not_in_1. Defined.

Hint Constructors ae_exp.


Lemma in_supp_union_iff (a b : PFin) k :
  In k (supp ((a ∪ b) : PFin)) <-> In k (supp a) \/ In k (supp b).
Proof.
  simpl;intuition;auto with set.
Qed.

Hint Resolve <- in_supp_union_iff : set.

Lemma fresh_union_iff (a b : PFin) (c : NomAtom) :
  c # (a ∪ b : PFin) <-> (c # a) /\ c # b.
Proof.
  split.
  + intros;unfold fresh in *; repeat rewrite Disjoint_spec in *.
      intuition; specialize (H k); apply H;
        intuition;auto with set.
  + intros;unfold fresh in *; repeat rewrite Disjoint_spec in *;simpl.
    intuition. specialize (H0 k). specialize (H1 k).
    simpl in *. intuition;auto with set.
    apply union_1 in H3. intuition;auto with set.
Qed.

Hint Resolve <- fresh_union_iff : nom.
Hint Resolve -> fresh_union_iff : nom.

Import Basics.

Lemma eq_dec_refl a : eq_dec a a = left eq_refl.
Proof.
  destruct (eq_dec a a). f_equal. apply UIP_nat.
  easy.
Qed.

Lemma eq_dec_neq a b : a <> b -> exists p, eq_dec a b = right p.
Proof.
  intros H.
  destruct (eq_dec a b);subst.
  + exists H;easy.
  + exists n;easy.
Qed.

Lemma eq_dec_neq' a b (Hneq : a <> b): Atom.eq_dec a b = right Hneq.
Proof.
  induction a; destruct b.
  - exfalso; auto.
  - simpl. f_equal. apply proof_irrelevance.
  - simpl. f_equal. apply proof_irrelevance.
  - simpl. destruct (Atom.eq_dec a b).
    + subst;exfalso;auto.
    + f_equal. apply proof_irrelevance.
Qed.

Example identity_alpha_equiv :
  forall x y, (Lam x (Var x)) =α (Lam y (Var y)).
Proof.
  intros x y.
  apply ae_lam with (vs:=empty).
  intros. simpl. unfold swap_fn.
  now repeat rewrite eq_dec_refl.
Qed.

(** ** Typing *)

(** Environments are defined inductively *)
Inductive Env {A : Type} : Type :=
  | empty : Env
  | cons  : Env -> NomAtom -> A -> Env.


Fixpoint lookEnv {T : Type} (E : Env) (x : Atom) : option T :=
  match E with
    | empty => None
    | cons E y A =>
      if Atom.eq_dec y x then Some A else lookEnv E x
  end.

Lemma lookEnv_cons :
  forall (x : NomAtom) (σ : Ty) (Gamma : Env) (x0 : NomAtom) (A : Ty),
    x <> x0 ->
    lookEnv Gamma x0 = Some A ->
    lookEnv (cons Gamma x σ) x0 = Some A.
Proof.
  intros x σ Gamma x0 A Hneq H.
  induction Gamma.
  + cbn in *. congruence.
  + cbn. destruct (Atom.eq_dec x x0);try congruence.
    cbn in *. destruct (Atom.eq_dec c x0);try congruence.
Qed.

Fixpoint ac_env {A : Type} (p : Perm) (e : Env (A:=A)) :=
  match e with
  | empty => empty
  | cons env a e => cons (ac_env p env) (p @ a) e
  end.

Fixpoint dom {A : Type} (env : Env (A:=A)) : PFin :=
  match env with
  | empty => Atom.V.empty
  | cons env1 a e => (singleton a) ∪ (dom env1)
  end.

(** Nominal set of environments*)
Instance NomEnv {A : Type} : NomSet.
  refine (
        {| Carrier := Env (A:=A);
           action := ac_env;
           supp := dom;
           action_id := _;
           action_compose := _;
           support_spec := _
        |}).
- (* action_id *)
  intros env. induction env.
  + reflexivity.
  + simpl. rewrite IHenv. reflexivity.
- (* action_compose *)
  intros env p p'. induction env.
  + reflexivity.
  + simpl. rewrite IHenv. reflexivity.
- (* support_spec *)
  intros p env H.
  induction env.
  + reflexivity.
  + simpl. 
    assert (Hdom : forall a0, In a0 (dom env) -> p a0 = a0) by
        (intros;apply H;simpl;auto with set).
    rewrite IHenv;auto.
    rewrite H. reflexivity. simpl. auto with set.
Defined.

(**  A typing context extension: *)
Notation "Gamma , a ::: A" := (cons Gamma a A) (at level 201).

Definition TEnv : Type := NomEnv (A:=Ty).
Reserved Notation "[ Gamma |- a ::: A ]".


(** The usual typing rules for the STLC *)
Inductive Typing : TEnv -> Exp -> NomTy -> Prop :=
  | tyInt : forall (Gamma : TEnv) (n : Atom),
      [ Gamma |- (Int n) ::: tInt]
  | tyVar : forall (Gamma : TEnv) (x : NomAtom) (A : Ty),
      lookEnv Gamma x = Some A ->
      [ Gamma |- (Var x) ::: A ]
  | tyLam : forall (Gamma : TEnv) (x : NomAtom) (b : Exp) (A B : Ty),
      x # Gamma ->
      [ Gamma, x ::: A |- b ::: B ] ->
      [ Gamma |- (Lam x b) ::: (A :-> B)]
  | tyApp : forall (Gamma : TEnv) (f a : Exp) (A B : Ty),
      [ Gamma |- f ::: (A :-> B) ]->
      [ Gamma |- a ::: A ] ->
      [ Gamma |- (App f a) ::: B ]
where "[ Gamma |- a ::: A ]" := (Typing Gamma a A).

Lemma lookEnv_In (Γ : TEnv) x τ:
  lookEnv Γ x = Some τ ->
  In x (supp Γ).
Proof.
  intros Hlook.
  induction Γ;cbn in *.
  + inversion Hlook.
  + destruct (Atom.eq_dec c x);auto with set.
Qed.

Lemma fresh_cons_env {A : Type} (Γ : @NomEnv A) (x y : NomAtom) (a : A):
  x # Γ ->
  x # y ->
  x # ((cons Γ y a) : NomEnv).
Proof.
  intros Hx Hxy.
  unfold fresh in *. cbn. rewrite Disjoint_spec in *.
  intros ??. rewrite TSetMod.OP.P.Dec.F.union_iff in *.
  specialize (Hx k).
  specialize (Hxy k).
  intuition;eauto with set.
Qed.

Lemma exchange x y τ σ1 σ2 (Γ : TEnv) e:
  x <> y ->
  x # Γ ->
  y # Γ ->
  [ Γ, x ::: σ1, y ::: σ2 |- e ::: τ ] ->
  [ Γ, y ::: σ2, x ::: σ1 |- e ::: τ ].
Proof.
  intros Hneq Hx Hy Hty.
  revert dependent Γ.
  revert dependent x.
  revert y σ1 σ2 τ.
  induction e;intros.
  + inversion Hty;constructor.
  + inversion Hty;subst;clear Hty;
      constructor;cbn in *.
    destruct (Atom.eq_dec y a), (Atom.eq_dec x a);subst;congruence.
  + cbn in *.
    inversion Hty;subst.
    apply tyLam.
    * unfold fresh in *;cbn in *.
      rewrite Disjoint_spec in *.
      intros ??. specialize (H2 k).
      apply H2.
      rewrite <- AtomN.V.union_assoc.
      replace (singleton y ∪ singleton x) with (singleton x ∪ singleton y)
        by apply AtomN.V.union_comm.
      now rewrite AtomN.V.union_assoc.
    * apply IHe;eauto with set.
      4 : { }
    assert (In x (supp Γ)) by (eapply lookEnv_In;eauto).
    destruct (Atom.eq_dec y x0).
    * subst. auto with set.


Lemma weakening' Γ x τ σ (e : Exp) :
  x # Γ ->
  [ Γ |- e ::: τ ] ->
  [ Γ, x ::: σ |- e ::: τ ].
Proof.
  intros Hx Hty.
  revert dependent x.
  revert σ.
  induction Hty.
  + constructor.
  + intros;constructor.
    assert (Ha : In x (supp Gamma)). admit.
    assert (Hneqx: ~ In x0 (supp Gamma)) by (apply not_in_set_fresh;eauto with set).
    assert (x0 <> x) by (apply not_eq_sym;eauto with set).
    now apply lookEnv_cons.
  + intros. constructor.
    * admit.
    * apply IHHty.
Admitted.


(** ** Equivariance of the typing relation  *)

(** First, we prove lemmas showing equivariance of functions and relations
involved in the definition of the typing relation *)

Lemma equivar_lookEnv (x : NomAtom) (env : NomEnv (A :=Ty)) ty p:
  lookEnv env x = Some ty -> lookEnv (p @ env) (p @ x) = Some ty.
Proof.
  intros.
  induction env.
  - inversion H.
  - simpl in *. destruct (Atom.eq_dec c x).
    + subst. destruct (Atom.eq_dec (p x) (p x)).
      * assumption.
      * exfalso. auto.
    + assert (Hneq : p c <> p x). unfold not.
      intros Heq. apply n. destruct p as [f g l r Hfin]. simpl in *.
      replace c with (g (f c)) by apply (happly l).
      replace x with (g (f x)) by apply (happly l).
      congruence.
      assert (Hpcx : Atom.eq_dec (p c) (p x) = right Hneq) by (apply eq_dec_neq';auto).
      rewrite Hpcx. apply IHenv. assumption.
Qed.

(** This property is not specific for the support of the elements of [TEnv].
    Ideally, we want such lemma for any nominal set, but not all the definitions of suport have this property.
    It classical setting it is possible with the definition of smallest support, but in type theory it is trickier *)
Lemma equivar_supp_env (e : NomAtom) (x : TEnv) p :  (supp (p @ x)) = (p @ (supp x : PFin)).
Proof.
  induction x.
  - simpl. apply set_extensionality.
    intros e'. split;auto with set.
  - simpl in *. rewrite IHx.
    apply set_extensionality.
    intros e'. split.
    + intros. rewrite set_map_iff in *. 
      rewrite TSetMod.OP.P.Dec.F.union_iff in *.
      rewrite set_map_iff in *.
      destruct H as [Heq|Htl].
      * exists c. split;try symmetry;auto with set.
      * destruct Htl as [e'' He''].
        exists e'';intuition;eauto with set.
    + intros. rewrite set_map_iff in *. 
      rewrite TSetMod.OP.P.Dec.F.union_iff in *.
      rewrite set_map_iff in *.
      destruct H as [e'' He'']. destruct He'' as [L R].
      rewrite TSetMod.OP.P.Dec.F.union_iff in *.
      destruct R.
      * left;subst. auto with set.
      * right. exists e''.
      subst. split;auto.
Qed.

Lemma equivar_fresh :
  equivar_rel (fun (a : NomAtom) (x : TEnv) => fresh a x).
Proof.
  unfold equivar_rel.
  intros. unfold fresh in *. rewrite Disjoint_spec in *.
  intros. unfold not. intros Hin.
  rewrite equivar_supp_env in *;auto.
  destruct p as [f g l r Hfin].
  simpl in *.
  rewrite set_map_iff in *.
  destruct Hin as [Hx He'].
  assert (k = f x) by (rewrite singleton_spec in *;auto).
  destruct He' as [e He']. intuition. subst.
  assert (x = e) by
      (replace e with (g (f e)) by apply (happly l);
       replace x with (g (f x)) by apply (happly l);
       congruence).
  apply (H x);intuition;subst;auto with set.
Qed.

(** Explicit proof of equivarience of the typing relation *)
Lemma equivar_Typing ty : equivar_rel (fun Gamma e => Typing Gamma e ty).
Proof.
  unfold equivar_rel.
  intros x y p Hty.
  induction Hty.
  - constructor.
  - constructor. apply equivar_lookEnv. assumption.
  - constructor. apply equivar_fresh. assumption.
    apply IHHty.
  - econstructor.
    + apply IHHty1.
    + apply IHHty2.
Qed.

(** We add the previous equivarience lemmas as hints *)
Hint Resolve equivar_lookEnv equivar_fresh.

(** The proof can be automated, since it basically uses the fact that all the 
    pieces envolved in the proof are equivariant *)
Lemma equivar_Typing_alt ty : equivar_rel (fun Gamma e => Typing Gamma e ty).
Proof.
  unfold equivar_rel.
  intros x y p Hty.
  induction Hty;econstructor;eauto.
Qed.

Lemma equivar_Typing_inv ty :
  forall (x : NomEnv) (y : NomExp) (p : Perm),
   [p @ x |- p @ y ::: ty] -> [x |- y ::: ty].
Proof.
  intros.
  (* specialize (equivar_Typing ty _ _ (- p) H) as HH. with (p:=perm_inv p) in H. *)
  (* unfold equivar_rel. *)
Admitted.

Lemma fresh_atom_neq_iff (a b : NomAtom) : a # b <-> a <> b.
Proof.
  split.
  + intros Hab. unfold fresh in *.
    rewrite TSetMod.Disjoint_spec in Hab;intuition; eauto with set.
  + intros H.
    unfold fresh in *.
    rewrite TSetMod.Disjoint_spec in *. intros ? H0.
    destruct H0.
    assert (a = k /\ b = k) by auto with set.
    intuition;tryfalse.
Qed.

Lemma fresh_atom_singleton (a b : NomAtom) : a # (singleton b : PFin) <-> a # b.
Proof.
  split;intros;eauto with set.
Qed.


Hint Resolve fresh_atom_singleton : set.
Hint Resolve <- fresh_atom_neq_iff : set.
Hint Resolve -> fresh_atom_neq_iff : set.

Lemma swap_compose_neq (a b c z : NomAtom) :
  b # z ->
  c # z ->
  (((swap b c ∘p swap a b) z) = ((swap a c) z)).
Proof.
  unfold swap, swap_fn, fresh;cbn.
  intros Hb Hc.
  assert (Hc_neq : c <> z) by auto with set.
  assert (b <> z) by auto with set.
  cbn in *. unfold fresh, swap_fn in *.
  destruct (eq_dec a z);
    destruct (eq_dec b z);subst;try rewrite eq_dec_refl;auto.
  destruct (eq_dec z a);tryfalse.
  destruct (eq_dec b z);tryfalse.
  destruct (eq_dec c z);tryfalse.
  reflexivity.
Qed.
  
Lemma swap_action_compose_fresh (a b c : NomAtom) (e : NomExp) :
  b # (supp e : PFin) ->
  c # (supp e : PFin) ->
  (((swap b c ∘p swap a b) @ e) = ((swap a c) @ e)).
Proof.
  intros Hb Hc.
  induction e;auto.
  + unfold swap_fn.
    assert (Hc_neq : c <> a0) by auto with set.
    assert (b <> a0) by auto with set.
    cbn. apply f_equal.
    now apply swap_compose_neq.
  + cbn in *. rewrite fresh_union_iff in *.
    assert (Hc_fresh : (c : NomAtom) # (a0 : NomAtom)) by (intuition;auto with set).
    assert (Hc_neq : c <> a0) by (destruct Hb;auto with set).
    assert (Hb_fresh : (c : NomAtom) # (a0 : NomAtom)) by (destruct Hb; auto with set).
    assert (Hb_neq : b <> a0) by (destruct Hb;auto with set).
    rewrite IHe;intuition;auto.
    apply f_equal2.
    * now apply swap_compose_neq.
    * reflexivity.
  + cbn in *.
    rewrite fresh_union_iff in *.
    apply f_equal2;intuition;auto.
Qed.

Lemma Exp_perm_ind (P : Exp -> Prop)
      (Hint : forall n : nat, P (Int n))
      (Hvar : forall a : Atom, P (Var a))
      (Hlam : forall (a : Atom) (e : Exp), (forall (π : Perm), P (π @ e)) -> P (Lam a e))
      (Happ : forall e : Exp, P e -> forall e0 : Exp, P e0 -> P (App e e0)) :
      forall e : Exp, P e.
Proof.
  intros e.
  assert (H : forall π, P (π @ e)).
  {induction e;intros;cbn;auto.
   cbn. apply Hlam with (a:=π a)(e:= @action NomExp π e).
   intros;rewrite action_compose. apply IHe. }
  rewrite <- (action_id (NomSet:=NomExp)).
  apply H.
Qed.

Lemma Exp_perm_rect (P : Exp -> Type)
      (Hint : forall n : nat, P (Int n))
      (Hvar : forall a : Atom, P (Var a))
      (Hlam : forall (a : Atom) (e : Exp), (forall (π : Perm), P (π @ e)) -> P (Lam a e))
      (Happ : forall e : Exp, P e -> forall e0 : Exp, P e0 -> P (App e e0)) :
      forall e : Exp, P e.
Proof.
  intros e.
  assert (H : forall π, P (π @ e)).
  {induction e;intros;cbn;auto.
   cbn. apply Hlam with (a:=π a)(e:= @action NomExp π e).
   intros;rewrite action_compose. apply IHe. }
  rewrite <- (action_id (NomSet:=NomExp)).
  apply H.
Defined.

Definition Exp_perm_rect' (P : Exp -> Type)
      (Hint : forall n : nat, P (Int n))
      (Hvar : forall a : Atom, P (Var a))
      (Hlam : forall (a : Atom) (e : Exp), (forall (π : Perm), P (π @ e)) -> P (Lam a e))
      (Happ : forall e : Exp, P e -> forall e0 : Exp, P e0 -> P (App e e0)) :
      forall (e : Exp) (π : Perm), P (π @ e).
  refine (fix go e := _).
  destruct e.
  - intros;apply Hint.
  - intros;apply Hvar.
  - intros π. cbn. apply Hlam with (a:=π a)(e:= @action NomExp π e).
    intros π0;rewrite action_compose. apply go.
  - intros π. apply Happ; fold ac_exp; apply go.
Defined.

Definition Exp_perm_rec {A}
           (Hint : nat -> A)
           (Hvar : Atom -> A)
           (Hlam : Atom -> Exp -> (Perm -> A) -> A)
           (Happ : Exp -> A -> Exp -> A -> A) : Exp -> Perm -> A :=
  Exp_perm_rect' (fun _ => A) Hint Hvar Hlam Happ.
  

Definition α_compatible (P : Exp -> Prop) : Prop
  := forall e1 e2, e1 =α e2 -> P e1 -> P e2.

Definition α_compatible_type (P : Exp -> Type) : Type
  := forall e1 e2, e1 =α e2 -> P e1 -> P e2.


Lemma ae_exp_equivariant :
  equivar_rel ae_exp.
Proof.
  intros e1 e2 π Hα.
  revert dependent π.
  induction Hα;intros π.
  + constructor.
  + constructor.
  + cbn. eapply ae_lam with (vs:= vs).
    intros. change (ac_exp π e1) with (π @ e1).
    rewrite action_compose.
Admitted.

Lemma ae_exp_refl (e : Exp) : e =α e.
Proof.
  induction e;try constructor;auto.
  apply ae_lam with (vs:=supp (e : NomExp)).
  intros.
  now apply ae_exp_equivariant.
Qed.

Lemma ae_exp_sym (e1 e2 : Exp) :
  e1 =α e2 ->
  e2 =α e1.
Proof.
  Admitted.

Lemma ae_exp_trans (e1 e2 e3 : Exp) :
  e1 =α e2 ->
  e2 =α e3 ->
  e1 =α e3.
Proof.
  Admitted.

(** ** An induction principle for α-compatible properties *)
(** In the [Lam] case, we use co-finite quantification: [P (Lam a a)] holds for all [a] apart from a finite set of variables [vs] *)
Lemma Exp_alpha_equiv_ind :
  forall P : Exp -> Prop,
    α_compatible P ->
    (forall n : nat, P (Int n)) ->
    (forall (a : NomAtom), P (Var a)) ->
    (exists (vs : PFin), forall (a : NomAtom),
          a # vs -> forall (e : Exp), P e -> P (Lam a e)) ->
    (forall e : Exp, P e -> forall e0 : Exp, P e0 -> P (App e e0)) ->
    forall e : Exp, P e.
Proof.
  intros ? Hα Hint Hvar Hlam Happ e.
  apply Exp_perm_ind;auto.
  + intros a e0 He0.
    destruct Hlam as [vs Hlam].
    unfold α_compatible in Hα.
    set (get_fresh (vs ∪ singleton a ∪ supp (e0 : NomExp))) as b.
    cbn in *.
    destruct b as [b fresh_b].
    repeat rewrite fresh_union_iff in fresh_b.
    destruct fresh_b as [[Hb_vs Hb_a] Hb_e0].
    set ((swap a b) @ (Lam a e0 : NomExp)) as M.
    assert (Mα : M =α Lam a e0).
    { cbn in M.
      eapply ae_lam with (vs:=supp (e0 : NomExp));auto.
      unfold swap_fn. rewrite eq_dec_refl.
      intros.
      change ((swap b c @ ((swap a b) @ e0)) =α (swap a c @ e0)).
      rewrite action_compose.
      rewrite swap_action_compose_fresh;auto.
      apply ae_exp_refl. }
    assert (H : P ((swap a b) @ (Lam a e0))).
      { apply Hlam.
        + cbn. unfold swap_fn. now rewrite eq_dec_refl.
        + apply He0. }
      specialize (Hα _ _ Mα).
      apply Hα. apply H.
Qed.

Lemma Exp_alpha_equiv_ind_ctx :
  forall (P : TEnv -> Atom -> Exp -> Prop),
    (forall ctx a, α_compatible (P ctx a)) ->
    (forall ctx a (n : nat), P ctx a (Int n)) ->
    (forall ctx a (a0 : NomAtom), P ctx a (Var a0)) ->
    (forall (ctx : TEnv) a, exists (vs : PFin),  forall (a0 : NomAtom),
        a0 # ((supp ctx ∪ vs ∪ singleton a) : PFin) ->
        forall (e : Exp), (forall ctx0 a1, P ctx0 a1 e) -> P ctx a (Lam a0 e)) ->
    (forall ctx a (e : Exp), P ctx a e -> forall e0 : Exp, P ctx a e0 -> P ctx a (App e e0)) ->
    forall ctx a (e : Exp), P ctx a e.
Proof.
  intros P Hα Hint Hvar Hlam Happ vs a e.
  revert a.
  revert vs.
  apply Exp_perm_ind with (P:=fun e => forall (ctx : TEnv) (a : Atom), P ctx a e);auto.
  + intros a0 e0 He0 ctx a.
    destruct (Hlam ctx a) as [vs0 Hlam'].
    unfold α_compatible in Hα.
    set (get_fresh (supp ctx ∪ vs0 ∪ singleton a ∪ singleton a0 ∪ supp (e0 : NomExp))) as b.
    cbn in *.
    destruct b as [b fresh_b].
    repeat rewrite fresh_union_iff in fresh_b.
    destruct fresh_b as [[[Hb_vs Hb_vs0] Hb_a] Hb_e0].
    set ((swap a0 b) @ (Lam a0 e0 : NomExp)) as M.
    assert (Mα : M =α Lam a0 e0).
    { cbn in M.
      eapply ae_lam with (vs:=supp (e0 : NomExp));auto.
      unfold swap_fn. rewrite eq_dec_refl.
      intros.
      change ((swap b c @ ((swap a0 b) @ e0)) =α (swap a0 c @ e0)).
      rewrite action_compose.
      rewrite swap_action_compose_fresh;auto.
      apply ae_exp_refl. }
    assert (H : P ctx a ((swap a0 b) @ (Lam a0 e0))).
      { apply Hlam'.
        + cbn. unfold swap_fn. rewrite eq_dec_refl.
          intuition;eauto with set.
        + intros ctx0. apply He0. }
      specialize (Hα ctx a _ _ Mα).
      apply Hα. apply H.
Qed.

Lemma Exp_alpha_equiv_rect :
  forall P : Exp -> Type,
    α_compatible_type P ->
    (forall n : nat, P (Int n)) ->
    (forall a : NomAtom, P (Var a)) ->
    ({vs : PFin & forall (a : NomAtom) (e : Exp),
          a # vs -> P e -> P (Lam a e)}) ->
    (forall e : Exp, P e -> forall e0 : Exp, P e0 -> P (App e e0)) ->
    forall e : Exp, P e.
Proof.
  intros ? Hα Hint Hvar Hlam Happ e.
  apply Exp_perm_rect;auto.
  intros a e0 He0.
  destruct Hlam as [vs Hlam].
  unfold α_compatible in Hα.
  (* set (get_fresh (vs ∪ singleton a ∪ supp (e0 : NomExp))) as b. *)
  set (get_fresh (vs ∪ supp (e0 : NomExp))) as b.
  cbn in *.
  destruct b as [b fresh_b].
  apply fresh_union_iff in fresh_b.
  (* repeat rewrite fresh_union_iff in fresh_b. *)
  destruct fresh_b.
    (* as [[Hb_vs Hb_a] Hb_e0]. *)
  set ((swap a b) @ (Lam a e0 : NomExp)) as M.
  assert (Mα : M =α Lam a e0).
  { cbn in M.
    eapply ae_lam with (vs:=supp (e0 : NomExp));auto.
    unfold swap_fn. rewrite eq_dec_refl.
    intros.
    change ((swap b c @ ((swap a b) @ e0)) =α (swap a c @ e0)).
    rewrite action_compose.
    rewrite swap_action_compose_fresh;auto.
    apply ae_exp_refl. }
  assert (Hswap : P ((swap a b) @ (Lam a e0))).
    { apply Hlam.
      + cbn. unfold swap_fn. now rewrite eq_dec_refl.
      + fold ac_exp. apply He0. }
    specialize (Hα _ _ Mα).
    apply Hα. apply Hswap.
Defined.

Definition Exp_alpha_rec {A}
           (Hint : nat -> A)
           (Hvar : Atom -> A)
           (Hlam : PFin * (Atom -> Exp -> A -> A))
           (Happ : Exp -> A -> Exp -> A -> A) : Exp -> A.
  refine (Exp_alpha_equiv_rect (fun _ => A) (fun _ _ _ => id) Hint Hvar _ Happ).
  destruct Hlam as [vs f].
  apply (existT _ vs).
  intros v e ? a0. exact (f v e a0).
Defined.

Definition get_canonical : Exp -> PFin -> Exp :=
   (Exp_alpha_rec (A:=PFin -> Exp)
    (fun n _ => Int n)
    (fun v _ => Var v)
    ((Atom.V.empty, fun v body f vs => Lam v (f (singleton v ∪ vs))))
    (fun e1 _ e2 _ _ => App e1 e2)).

Example test_alpha_rec1 x :
  get_canonical (Lam x (Var x)) Atom.V.empty = (Lam x (Var x)).
Proof.
  cbn.
  set ((Atom.V.empty ∪ singleton (id x)) ∪ singleton (id x)) as rr.
  destruct (get_fresh _).
  destruct (fresh_union_iff _ _ ).
  destruct a. unfold id, swap_fn.
  rewrite eq_dec_refl.
Abort.

Example nested_lam_alpha_equiv :
  forall x y, (Lam y (Lam x (Var x))) =α (Lam x (Lam x (Var x))).
Proof.
  intros x y.
  apply ae_lam with (vs:=AtomN.V.empty).
  intros. simpl. unfold swap_fn.
  repeat rewrite eq_dec_refl.
  destruct (eq_dec x y).
  - eapply ae_lam with (vs:=AtomN.V.empty). intros. unfold swap, swap_fn;cbn.
    now repeat rewrite eq_dec_refl.
  - destruct (eq_dec c y).
    * eapply ae_lam with (vs:=AtomN.V.empty). intros. unfold swap, swap_fn;cbn.
      now repeat rewrite eq_dec_refl.
    * eapply ae_lam with (vs:=AtomN.V.empty). intros. unfold swap, swap_fn;cbn.
    now repeat rewrite eq_dec_refl.
Qed.

Lemma Typing_is_NOT_α_compatible (x y : NomAtom) :
  x # y ->
  (forall Γ τ, α_compatible (fun e => [ Γ |- e ::: τ ])) -> False.
Proof.
  intros Hfresh H. unfold α_compatible in H.
  set (Lam x (Lam x (Var x))) as e1.
  set (Lam y (Lam x (Var x))) as e2.
  assert (typed_e2 : [empty |- e2 ::: tInt :-> (tInt :-> tInt) ]).
  { repeat constructor; try easy.
    unfold fresh in *. cbn. now rewrite eq_dec_refl. }
  assert (Hα : e2 =α e1) by apply nested_lam_alpha_equiv.
  specialize (H empty _ _ _ Hα typed_e2) as Hfalse.
  inversion Hfalse;subst.
  inversion H6;subst.
  unfold fresh in *.
  rewrite AtomN.V.Disjoint_spec in *.
  specialize (H5 x).
  intuition;eauto with set.
Qed.


(** New typing rules for the STLC, with α-equivalence for lambdas *)
Inductive Typing_α : TEnv -> Exp -> NomTy -> Prop :=
  | tyInt_α : forall (Gamma : TEnv) (n : Atom),
      [ Gamma |- (Int n) ::: tInt]
  | tyVar_α : forall (Gamma : TEnv) (x : NomAtom) (A : Ty),
      lookEnv Gamma x = Some A ->
      [ Gamma |- (Var x) ::: A ]
  | tyLam_α : forall (Gamma : TEnv) (x y : NomAtom) (b1 b2 : Exp) (A B : Ty),
      y # Gamma ->
      (Lam x b2) =α (Lam y b1) ->
      [ Gamma, y ::: A |- b1 ::: B ] ->
      [ Gamma |- (Lam x b2) ::: (A :-> B)]
  | tyApp_α : forall (Gamma : TEnv) (f a : Exp) (A B : Ty),
      [ Gamma |- f ::: (A :-> B) ]->
      [ Gamma |- a ::: A ] ->
      [ Gamma |- (App f a) ::: B ]
where "[ Gamma |- a ::: A ]" := (Typing_α Gamma a A).

Example shadowing_typable x :
  [empty |- (Lam x (Lam x (Var x))) ::: tInt :-> (tInt :-> tInt) ].
Proof.
  set (get_fresh (singleton x)) as c.
  destruct c as [y Hy].
  eapply tyLam_α with (y:=y) (b1:=(Lam x (Var x)));try easy.
  apply ae_exp_sym.
  apply nested_lam_alpha_equiv.
  eapply tyLam_α with (y:=x) (b1:=(Var x)).
  + apply fresh_cons_env;auto with set.
    unfold fresh in *.
    rewrite Disjoint_spec in *;intros ??.
    specialize (Hy k). destruct H. eauto with set.
    rewrite fresh_atom_singleton in Hy.
    eauto with set.
    rewrite fresh_atom_neq_iff in *.
    now apply not_eq_sym.
  + apply ae_exp_refl.
  + repeat constructor. cbn. now rewrite eq_dec_refl.
Qed.

Lemma Typing_α_compatible Γ τ:
  α_compatible (fun e => [ Γ |- e ::: τ ]).
Proof.
  intros e1 e2 H Hτ.
  revert dependent e2.
  induction Hτ;intros e2 Ha;inversion Ha;subst;clear Ha.
  + constructor.
  + now constructor.
  + inversion H0;subst.
    set (get_fresh (vs ∪ vs0 ∪ supp (e0 : NomExp) ∪ supp Gamma)) as c.
    destruct c as [c Hc].
    repeat rewrite fresh_union_iff in *.
    destruct Hc as [[[Hvs Hvs0] He0] HΓ].
    eapply tyLam_α with (y:=y) (b1:=b1);auto.
    eapply ae_lam with (vs:=vs ∪ vs0).
    intros.
    repeat rewrite fresh_union_iff in *.
    destruct H1 as [Hc0_vs Hc0_vs0].
    specialize (H4 _ Hc0_vs).
    specialize (H2 _ Hc0_vs0).
    apply ae_exp_sym in H4.
    eapply ae_exp_trans;eauto.
  + econstructor;eauto.
Qed.

Definition weakening Γ x τ σ (e : Exp) : Prop :=
  x # Γ ->
  [ Γ |- e ::: τ ] ->
  [ Γ, x ::: σ |- e ::: τ ].

Lemma weakening_α_compatible Γ x τ σ :
  α_compatible (weakening Γ x τ σ).
Proof.
  intros e1 e2 Hα He1 Hx He2.
  apply ae_exp_sym in Hα.
  specialize (Typing_α_compatible Γ τ _ _ Hα) as H;cbn in *.
  unfold weakening in *.
  assert (Hwτ : [ Γ, x ::: σ |- e1 ::: τ]) by auto.
  apply ae_exp_sym in Hα.
  specialize (Typing_α_compatible (cons Γ x σ) τ _ _ Hα) as HH;cbn in *.
  auto.
Qed.

Hint Constructors Typing_α.

(* Lemma lookupEnv_fresh Γ x y τ: *)
(*   x # Γ -> *)
(*   lookEnv Γ  *)
  

Hint Resolve <- not_in_set_fresh.



Lemma weakening_Typing_α e Γ x:
  (forall τ σ, weakening Γ x τ σ e).
Proof.
  (* apply Exp_alpha_equiv_ind. *)
  (* apply Exp_alpha_equiv_ind. *)
  apply (@Exp_alpha_equiv_ind_ctx (fun Γ x e => forall τ σ,  weakening Γ x τ σ e)).
  + admit. (* apply weakening_α_compatible. *)
  + intros ? ? ? ? ? ? Hty. inversion Hty;subst;auto.
  + intros Γ0 ? a0 ? ? ? Hty. inversion Hty;subst;clear Hty.
    assert (Ha : In a0 (supp Γ0)). admit.
    assert (Hx: ~ In a (supp Γ0)) by eauto with set.
    assert (a <> a0) by (apply not_eq_sym;eauto with set).
    constructor.
    cbn. now destruct (Atom.eq_dec a a0);tryfalse.
  + intros Γ0 a. exists (singleton x).
    (* exists (supp Γ). *)
    intros a0 Hax e0 Hwe0 τ σ Hx Hty.
    unfold weakening in *.
    inversion Hty;subst;clear Hty.
    assert (Ha_fresh : (a0 # (supp Γ0 : PFin) /\ a0 # (singleton x : PFin)) /\ a0 # (singleton a : PFin)) by now repeat rewrite <- fresh_union_iff.
    eapply tyLam_α with (y:=a) (b1:=b1).
    * apply fresh_cons_env;intuition;auto.
    * apply ae_exp_refl.
    * apply Hwe0.
      ** apply fresh_cons_env;intuition;eauto with set.
      ** eapply Typing_α_compatible.
         inversion H3;subst.
      unfold fresh;cbn. unfold AtomN.V.Disjoint. intuition;eauto with set.
      unfold fresh. cbn.
    rewrite Disjoint_spec.
    intros ??.
    rewrite SetProperties.P.add_union_singleton in *.
    eauto with set.
    
    

