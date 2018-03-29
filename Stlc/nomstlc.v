Require Import PeanoNat.
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
  | Int : Atom -> Exp
  | Var : Atom -> Exp
  | Lam : Atom -> Exp -> Exp
  | App : Exp -> Exp -> Exp.

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
  | Lam v e1 => add v (supp_exp e1)
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
    intros a Ha. apply H. simpl;auto with set.
  + simpl.
    assert (He1 : forall a, In a (supp_exp e1) -> perm p a = a) by
        (intros;apply H;simpl;auto with set).
    assert (He2 : forall a, In a (supp_exp e2) -> perm p a = a) by
        (intros;apply H;simpl;auto with set).    
    rewrite IHe1;auto.
    rewrite IHe2;auto.
Defined.

(** ** Alpha-equivalence *)

(** We intruduce the following notation [a # (a1,a2,...,an)] 
    denotiong that the atom [a] is fresh for all the elements in the n-tuple.
    That is, [ (a # a1) /\ (a # a2) ... /\ (a # an)] *)
Notation "a # '(' a1 , .. , an ')'" :=
  ((and (fresh a a1)) .. (and (fresh a an) True) ..) (at level 40).
Reserved Notation "e1 =α e2" (at level 80).

Inductive ae_exp : NomExp -> NomExp -> Prop :=
| ae_int : forall n,
    (Int n) =α (Int n)
| ae_var : forall (a : NomAtom),
    (Var a) =α (Var a)
| ae_lam : forall (a b c : NomAtom) (e1 e2 : NomExp),
    c # (a, b, fv_exp e1, fv_exp e2) ->
    ((swap a c) @ e1) =α ((swap b c) @ e2) ->
    (Lam a e1) =α (Lam b e2)
| ae_app : forall e1 e2 e1' e2',
    e1 =α e1' ->
    e2 =α e2' ->
    (App e1 e2) =α (App e1' e2')
where "e1 =α e2" := (ae_exp e1 e2).

Lemma eq_dec_refl a : Atom.eq_dec a a = left eq_refl.
Proof.
  induction a;auto. simpl. rewrite IHa. auto.
Qed.

Lemma eq_dec_neq a b (Hneq : a <> b): Atom.eq_dec a b = right Hneq.
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
  destruct (Atom.Atom_inf (union (singleton x) (singleton y))) as [z Hz].
  assert (Hneq : z <> x /\ z <> y) by
      (split; unfold not; intros; apply Hz; auto with set).
  apply ae_lam with (c:=z); repeat split;
    try (simpl; unfold fresh; rewrite Disjoint_spec; intros u;
         unfold not; intros; apply Hz; simpl in *; repeat rewrite singleton_spec in *).
  - assert (z = x) by (destruct H; congruence).
    subst. intuition;tryfalse.
  - assert (z = y) by (destruct H; congruence).
    subst. intuition;tryfalse.
  - assert (z = x) by (destruct H; simpl in *;  congruence).
    subst. intuition;tryfalse.
  - assert (z = y) by (destruct H; simpl in *;  congruence).
    subst. intuition;tryfalse.
  - simpl. unfold swap_fn.
    destruct Hneq as [L R].
    assert (H : SetProperties.P.FM.eq_dec z x = right L) by apply eq_dec_neq.
    rewrite H.
    assert (H' : SetProperties.P.FM.eq_dec z y = right R) by apply eq_dec_neq.
    rewrite H'.
    repeat rewrite eq_dec_refl.
    constructor.
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


Fixpoint ac_env {A : Type} (p : Perm) (e : Env (A:=A)) :=
  match e with
  | empty => empty
  | cons env a e => cons (ac_env p env) (p @ a) e
  end.

Fixpoint dom {A : Type} (env : Env (A:=A)) : PFin :=
  match env with
  | empty => Atom.V.empty
  | cons env1 a e => add a (dom env1)
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
      assert (Hpcx : Atom.eq_dec (p c) (p x) = right Hneq) by (apply eq_dec_neq;auto).
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
      rewrite TSetMod.OP.P.Dec.F.add_iff in *.
      rewrite set_map_iff in *.
      destruct H as [Heq|Htl].
      * exists c. split;intuition;auto with set.
      * destruct Htl as [e'' He''].
        exists e'';intuition;eauto with set.
    + intros. rewrite set_map_iff in *. 
      rewrite TSetMod.OP.P.Dec.F.add_iff in *.
      rewrite set_map_iff in *.
      destruct H as [e'' He'']. destruct He'' as [L R].
      rewrite TSetMod.OP.P.Dec.F.add_iff in *.
      destruct R.
      * left;subst;congruence.
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
