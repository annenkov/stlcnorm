(** * Normalization of the Call-by-Value Simply-Typed Lambda Calculus. *)

(** #<div class="authors"># *)
(** Authors: Martin Elsman and Danil Annenkov, University of Copenhagen *)
(** #</div>#  *)

(** In the present formalization, we consider simply-typed lambda calculus (STLC) with 
    primitive type of integers. We show how to prove the normalization property of STLC
    using the Tait's method. The key observation is that we can define logical relation
    required for the proof of normalization using Coq's fixpoint *)

Require Import String.

(** ** Basic definitions *)

Inductive Ty : Set :=
  | tInt : Ty
  | tArr : Ty -> Ty -> Ty.

Notation "A :-> B" := (tArr A B) (at level 70).

(** The syntax for STLC. We use Coq's [string] type to represent variable names *)
Inductive Exp : Set :=
  | Int : nat -> Exp
  | Var : string -> Exp
  | Lam : string -> Exp -> Exp
  | App : Exp -> Exp -> Exp.

(** Environments are defined inductively *)
Inductive Env {A:Set} : Set :=
  | empty : Env
  | cons  : Env -> string -> A -> Env.

(** We have two kinds of notation for environment extension. *)

(**  A typing context extension: *)
Notation "Gamma , a @ A" := (cons Gamma a A) (at level 201).
(** A value environment extension: *)
Notation "E # [ a ~> v ]" := (cons E a v) (at level 99).

Fixpoint lookEnv {T : Set} (E : Env) (x : string) : option T :=
  match E with
    | empty => None
    | cons E y A =>
      if string_dec y x then Some A else lookEnv E x
  end.

Definition TEnv : Set := Env (A:=Ty).
Reserved Notation "[ Gamma |- a @ A ]".

(** The usual typing rules for the STLC *)
Inductive Typing : TEnv -> Exp -> Ty -> Prop :=
  | tyInt : forall (Gamma : TEnv) (n : nat),
      [ Gamma |- (Int n) @ tInt]
  | tyVar : forall (Gamma : TEnv) (x : string) (A : Ty),
      lookEnv Gamma x = Some(A) ->
      [ Gamma |- (Var x) @ A ]
  | tyLam : forall (Gamma : TEnv) (x : string) (b : Exp) (A B : Ty),
      [ Gamma, x @ A |- b @ B ] ->
      [ Gamma |- (Lam x b) @ (A :-> B)]
  | tyApp : forall (Gamma : TEnv) (f a : Exp) (A B : Ty),
      [ Gamma |- f @ (A :-> B) ]->
      [ Gamma |- a @ A ] ->
      [ Gamma |- (App f a) @ B ]
where "[ Gamma |- a @ A ]" := (Typing Gamma a A).


(** The values are either an integer or a closure, corresponding to a lambda abstraction *)
Inductive Val : Set :=
  | vInt  : nat -> Val
  | vClos : Env (A:=Val) -> string -> Exp -> Val.

Definition DEnv := Env (A:=Val).

Reserved Notation "[ E |- a ==> v ]".

(** We define big-step evaluation relation in a call-by-value style. 
    We do not use substitution, instead we are explicitly passing 
    a value environment *)
Inductive Eval : DEnv -> Exp -> Val -> Prop :=
  | eInt : forall (E : DEnv) (n : nat),
      [ E |- (Int n) ==> (vInt n) ]
  | eVar : forall (E : DEnv) (x : string) (v : Val),
      lookEnv E x = Some v ->
      [ E |- (Var x) ==> v ]
  | eLam : forall (E : DEnv) (x : string) (a : Exp),
      [ E |- (Lam x a) ==> (vClos E x a) ]
  | eApp : forall (E E0 : DEnv) (f a e0 : Exp) (v va : Val) (x : string),
      [ E |- f ==> (vClos E0 x e0) ] ->
      [ E |- a ==> va ] ->
      [ E0 # [x ~> va] |- e0 ==> v ] ->
      [ E |- (App f a) ==> v ]
where "[ E |- a ==> v ]" := (Eval E a v).

(** ** The logical relation *)

Reserved Notation "[ |= v @ t ]".

(** The very core of our proof of normalization is a logical relation, 
    defined recursively on a structure of types in our STLC *)
Fixpoint Equiv (val:Val) (ty:Ty) : Prop :=
  match ty with
      tInt => exists n : nat, val = (vInt n)
    | tArr A B => exists (x:string) (a:Exp) (E:DEnv),
                  (val = vClos E x a) /\
                  (forall v1:Val, [ |= v1 @ A ] ->
                                  exists v2:Val, [ E # [x ~> v1] |- a ==> v2] /\ [ |= v2 @ B ])
  end
where "[ |= v @ t ]" := (Equiv v t).
(** It is crucial to use a fixpoint for the definition of [Equiv], 
    because naive inductive definition will not pass strict positivity check *)

Notation "[ |= v @ t ]" := (Equiv v t).

Definition EquivEnv (E : DEnv) (Gamma : TEnv) : Prop :=
  (forall (x:string) (val:Val),
      lookEnv E x = Some val ->
      exists ty:Ty, lookEnv Gamma x = Some ty /\ [ |= val @ ty ])
  /\
  (forall (x:string) (ty:Ty),
      lookEnv Gamma x = Some ty ->
      exists val:Val, lookEnv E x = Some val /\ [ |= val @ ty ]).

Notation "[ |== E @ Gamma ]" := (EquivEnv E Gamma).

Lemma Look : forall (Gamma : TEnv) (ty : Ty) (E : DEnv) (s : string),
    [ |== E @ Gamma ] -> lookEnv Gamma s = Some ty
    -> exists v:Val, lookEnv E s = Some v /\ [ |= v @ ty ].
Proof.
  intros. unfold EquivEnv in H. intuition;auto.
Qed.

Lemma EquivExtend : forall (Gamma : TEnv) (E : DEnv) (s : string) (val : Val) (ty : Ty),
    [ |= val @ ty ] -> [ |== E @ Gamma ] -> [ |== (E # [s ~> val]) @ Gamma, s @ ty].
Proof.
  intros Gamma E s v ty Hty Heqv. constructor; intros s' v' E'; simpl in *.
  - remember (string_dec s s') as b.
    destruct b.
    + inversion E';subst. eexists. split;auto.
    + inversion Heqv as [H1 H2]. destruct (H1 s' v' E'). destruct H.
      eexists. split;eauto.
  - remember (string_dec s s') as b.
    destruct b.
    + inversion E';subst. eexists. split;auto.
    + inversion Heqv as [H1 H2]. destruct (H2 s' v' E'). destruct H.
      eexists. split;eauto.
Qed.

(** ** Normalization *)

Hint Constructors Typing Eval.

(** A tactic for repeatedly destructing all existentials in hypothesis [H], 
    creating new variables with the [n] preffix *)
Ltac dest_exs H n :=
  match goal with
  | [_ : ex _ |- _ ] => let i := fresh n in
                          let Hi := fresh "H" i in (destruct H as [i Hi]; dest_exs Hi n)
  | [_ : _ |- _] => idtac
  end.

(** A proof of normalization by induction on typing derivation. We are being very
    explicit in this proof and use proof automation only in obvious and tedious cases. *)
Lemma Normalisation : forall (exp : Exp) (Gamma : TEnv) (ty : Ty) (E : DEnv),
    [ Gamma |- exp @ ty ] -> [ |== E @ Gamma ] ->
    exists val:Val, [ E |- exp ==> val ] /\ [ |= val @ ty ].
Proof.
  intros until E. intros Ty He.
  generalize dependent E.
  induction Ty; intros E He.
  - exists (vInt n). split; auto. econstructor;eauto.
  - inversion He as [H1 H2]. destruct (H2 x A H) as [v H3]. destruct H3.
    exists v. split;auto.
  - exists (vClos E x b). split;auto.
    simpl. exists x. exists b. exists E. split;auto.
    intros v1 Hv1. specialize IHTy with (E:= E # [x ~> v1]). apply IHTy.
    apply EquivExtend; auto.
  - destruct (IHTy1 E He) as [v H]. clear IHTy1.
    destruct (IHTy2 E He) as [v' H']. clear IHTy2.
    destruct H as [? Heqv]. destruct H' as [? Heqv']. simpl in *. dest_exs Heqv x.
    destruct Hx1 as [Hveq H3].
    destruct (H3 v' Heqv') as [v'' H''].
    destruct H''. subst.
    exists v''; split; eauto.
Qed.

(** An alternative proof of normalization by induction on syntax *)
Lemma Normalisation_alt : forall (exp : Exp) (Gamma : TEnv) (ty : Ty) (E : DEnv),
    [ Gamma |- exp @ ty ] -> [ |== E @ Gamma ] ->
    exists val:Val, [ E |- exp ==> val ] /\ [ |= val @ ty ].
Proof.
  induction exp; intros Gamma ty E Ty Heqv.
  - exists (vInt n). split; auto.
    inversion Ty. exists n. reflexivity.
  - inversion_clear Ty. inversion Heqv as [H1 H2].
    specialize H2 with (x:=s)(ty:=ty).
    destruct (H2 H). exists x. intuition.
  - exists (vClos E s exp). split. constructor.
    inversion_clear Ty. exists s. exists exp. exists E. split;auto. 
    intros v1 Hv1. specialize IHexp with (Gamma:=cons Gamma s A)(ty:=B)(E:=cons E s v1).
    destruct (IHexp H).
    apply EquivExtend;auto. exists x. intuition.
  - inversion_clear Ty.
    specialize IHexp1 with (Gamma:=Gamma)(ty:= A :-> ty) (E:=E).
    specialize IHexp2 with (Gamma:=Gamma)(ty:=A)(E:=E).
    destruct (IHexp1 H Heqv) as [v1 Hv1]. clear IHexp1.
    destruct (IHexp2 H0 Heqv) as [v2 Hv2]. clear IHexp2.
    destruct Hv1 as [Ev1 Heqv1]. destruct Hv2 as [Ev2 Tv2].
    simpl in *. dest_exs Heqv1 x. destruct Hx1 as [Hv1 Heqv2]. subst.
    assert (H' := Heqv2 v2 Tv2). destruct H' as [v' Hv']. destruct Hv'.
    exists v'. split.
    * econstructor; eauto.
    * eauto.
Qed.
