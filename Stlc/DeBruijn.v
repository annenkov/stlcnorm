(* STLC with the de Bruijn reperesntation of variables *)

Require Import MetaCoq.Template.All.
From Coq Require Import List.

Require StlcCCC.

Import ListNotations.
Import MonadNotation.

Module IEnc := StlcCCC.

(** ** Basic definitions *)

Inductive Ty : Set :=
  | tU : Ty
  | tArr : Ty -> Ty -> Ty.

Fixpoint eq_Ty (τ σ : Ty) : bool :=
  match τ,σ with
  | tU, tU => true
  | tArr τ1 σ1, tArr τ2 σ2 => eq_Ty τ1 τ2 && eq_Ty σ1 σ2
  | _, _ => false
  end.

Program Fixpoint decidable_eq_Ty (τ σ : Ty) : {τ = σ} + {τ <> σ}  :=
  match τ,σ with
  | tU, tU => left eq_refl
  | tArr τ1 σ1, tArr τ2 σ2 => match decidable_eq_Ty τ1 τ2, decidable_eq_Ty σ1 σ2 with
                             | left H1, left H2 => left (ltac:(easy))
                             | right H1 ,left H2
                             | left H1, right H2
                             | right H1, right H2 => right (ltac:(easy))
                             end
  | tU, tArr _ _ => right (ltac:(easy))
  | tArr _ _, tU  => right (ltac:(easy))
  end.

Lemma eq_Ty_eq {τ σ : Ty} : eq_Ty τ σ = true -> τ = σ.
Proof.
  revert σ.
  induction τ;intros σ H.
  - destruct σ;auto;cbn in *. inversion H.
  - destruct σ;auto;cbn in *.
    * inversion H.
    * rewrite Bool.andb_true_iff in *.
      destruct H. apply f_equal2;auto.
Qed.


(** The syntax for STLC. We use Coq's natural numbers to represent variable indices *)
Inductive Exp : Set :=
  | Star : Exp
  | Rel  : nat -> Exp
  | Lam  : Ty -> (* type of the domain *)
           Exp -> (* abstraction's body *)
           Exp
  | App  : Exp -> Exp -> Exp.

Fixpoint to_ienc_types (τ : Ty) : IEnc.Ty :=
  match τ with
  | tU => IEnc.tU
  | tArr σ1 σ2 => IEnc.tArr (to_ienc_types σ1) (to_ienc_types σ2)
  end.

Definition to_iecn_ctx : list Ty -> IEnc.Ctx :=
  map to_ienc_types.

Definition nth_In {A} i (xs : list A) v:
  nth_error xs i = Some v -> IEnc.In v xs.
  intros H.
  revert dependent xs.
  induction i;intros xs H.
  - destruct xs.
    * inversion H.
    * cbn in *. inversion H. subst. constructor.
  - destruct xs;cbn in *.
    * inversion H.
    * auto.
Defined.

Definition nth_error_to_ienc_ctx Γ i τ:
  nth_error Γ i = Some τ ->
  nth_error (to_iecn_ctx Γ) i = Some (to_ienc_types τ).
  revert Γ τ.
  induction i.
  - intros. destruct Γ. inversion H.
    cbn in *. inversion H. now subst.
  - intros. destruct Γ. inversion H.
    cbn in *. inversion H. now subst.
Defined.

Fixpoint type_of (Γ : list Ty) (e : Exp) : option Ty :=
  match e with
  | Star => Some tU
  | Rel i => nth_error Γ i
  | Lam τ body => σ <- type_of (τ :: Γ) body;;
                  Some (tArr τ σ)
  | App u v => mlet σ <- type_of Γ u;;
               match σ with
               | tArr τ σ0 => τ0 <- type_of Γ v;;
                             if decidable_eq_Ty τ τ0 then Some σ0
                             else None
               | _ => None
               end
  end.

Example type_of_id :
  type_of [] (Lam tU (Rel 0)) = Some (tArr tU tU).
Proof. reflexivity. Qed.


Example type_of_id_applied :
  type_of [] (App (Lam tU (Rel 0)) Star) = Some tU.
Proof. reflexivity. Qed.

Definition to_ienc (Γ : list Ty) (e : Exp)
  : match type_of Γ e with
    | Some τ => IEnc.Exp (to_iecn_ctx Γ) (to_ienc_types τ)
    | None => unit
    end.
  revert Γ e.
  fix go 2.
  intros Γ e.
  refine
    (match e with
     | Star => IEnc.Star
     | Rel i => _
     (* match nth_error Γ i as o return nth_error Γ i = o -> _ with *)
     (* | Some τ => fun H => _ *)
     (* | None => fun H => _ *)
     (* end eq_refl *)
     | Lam τ body => _
     (* match type_of body with *)
     (*            | Some (existT _ Γ (existT _  _)) *)
     | App x x0 => _
     end).
  - cbn. destruct (nth_error Γ i) eqn:H.
    * apply IEnc.Var.
      apply (nth_In i).
      now apply nth_error_to_ienc_ctx.
    * exact tt.
  - cbn. destruct (type_of (τ :: Γ) body) eqn:Heq.
    * apply IEnc.Lam. specialize (go (τ :: Γ) body).
      rewrite Heq in go. apply go.
    * exact tt.
  - cbn.
    destruct (type_of Γ x) eqn:Heq.
    * destruct t.
      ** exact tt.
      ** destruct (type_of Γ x0) eqn:Heq0.
         *** destruct (decidable_eq_Ty t1 t) eqn:Hty.
             apply (IEnc.App (τ:=to_ienc_types t1)).
             specialize (go Γ x). rewrite Heq in go.
             apply go.
             specialize (go Γ x0). rewrite Heq0 in go. subst.
             apply go.
             exact tt.
         ***exact tt.
    * exact tt.
Defined.

Compute (to_ienc [] (Lam tU (Rel 0)) : IEnc.Exp [] (IEnc.tArr IEnc.tU IEnc.tU)).

Compute (to_ienc [] (App (Lam tU (Rel 0)) Star) : IEnc.Exp [] IEnc.tU).
