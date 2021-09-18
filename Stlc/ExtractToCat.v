From Coq Require Import String List.

Require StlcCCC.
Require Import DeBruijn.
From MetaCoq Require Import Template.Loader.
From MetaCoq Require Template.Ast.

From Categories Require Import Category.Main Basic_Cons.CCC
     Basic_Cons.Product Notations Coq_Cats.Type_Cat.Type_Cat Coq_Cats.Type_Cat.CCC.

Import ListNotations.
Import BasicAst.

Import monad_utils.
Import MonadNotation.

Open Scope string.

(** Extracts a constant name, inductive name or returns None *)
Definition to_kername (t : Ast.term) : option kername :=
  match t with
  | Ast.tConst c _ => Some c
  | Ast.tInd c _ => Some c.(inductive_mind)
  | _ => None
  end.

Notation "<%% t %%>" :=
  (ltac:(let p y :=
             let e := eval cbv in (to_kername y) in
             match e with
             | @Some _ ?kn => exact kn
             | _ => fail "not a name"
             end in quote_term t p)).

Module Coq := Template.Ast.

Unset Universe Polymorphism.

Module Examples.
  Import StlcCCC.

  Definition id_func_stlc : DeBruijn.Exp := (DeBruijn.Lam DeBruijn.tU (Rel 0)).
  Definition unquote_id := interpExp (C:=Type_Cat) (to_ienc [] id_func_stlc).

  Example unquote_id_id : unquote_id tt = (fun x :unit => x).
  Proof. reflexivity. Qed.
End Examples.

Fixpoint to_stlc_type (t : Coq.term) : option Ty :=
  match t with
  | Coq.tInd (mkInd nm _) _ => if eq_kername nm <%% unit %%> then
                                Some tU
                              else None
  | Coq.tProd _ dom codom => τ <- to_stlc_type dom;;
                             σ <- to_stlc_type codom;;
                             ret (tArr τ σ)
  | _ => None
  end.

Definition to_stcl_ctor (ind : inductive) (ctor_ind : nat) : option Exp :=
  if eq_kername ind.(inductive_mind) <%% unit %%> then
    Some Star
  else None.

Fixpoint mk_stlc_apps (u : Exp) (vs : list Exp) : Exp :=
  match vs with
  | [] => u
  | v :: vs0 => mk_stlc_apps (App u v) vs0
  end.

Fixpoint to_stlc (t : Coq.term) : option DeBruijn.Exp :=
  match t with
  | Coq.tRel i => Some (Rel i)
  | Coq.tLambda _ dom body =>
    τ <- to_stlc_type dom;;
    e <- to_stlc body;;
    ret (Lam τ e)
  | Coq.tApp f args =>
    u <- to_stlc f;;
    vs <- monad_map to_stlc args;;
    Some (mk_stlc_apps u vs)
  | Coq.tConstruct ind i _ => to_stcl_ctor ind i
  | _ => None
  end.

MetaCoq Quote Definition id_unit_syn := (fun x : unit => x).

Example id_unit_to_stlc :
  to_stlc id_unit_syn = Some (Lam tU (Rel 0)).
Proof. reflexivity. Qed.

MetaCoq Quote Definition id_unit_applied_syn :=
  ((fun x : unit => x) tt).

Example id_unit_applied_to_stlc :
  to_stlc id_unit_applied_syn = Some (App (Lam tU (Rel 0)) Star).
Proof. reflexivity. Qed.

Program Definition to_CCC {A} (name : string) (prog : A) : Core.TemplateMonad unit :=
  t <- Core.tmQuote prog;;
  res <- Core.tmEval Common.lazy (to_stlc t);;
  match res with
  | Some e => _
  | None => Core.tmFail "Not a valid STLC term"
  end.
Next Obligation.
  destruct (type_of [] e) eqn:Hty.
  - set (to_ienc [] e) as ienc_e.
    rewrite Hty in ienc_e. cbn in *.
    apply (res <- Core.tmEval Common.lazy
                             (fun (C : Category) (HC : CCC C) => StlcCCC.interpExp (C:=C) ienc_e);;
         Core.tmDefinition name res;;
         ret tt).
  - exact (Core.tmFail "Not a well-typed STLC term").
Defined.

Definition cprod {C : Category} {HP : @Has_Products C} (A B : C) : Product A B := HP A B.

Notation "f △ g" := (@Prod_morph_ex _ _ _ _ _ f g) (at level 50): morphism_scope.

Notation "'cur' f" := (Exp_morph_ex _ _ f) (at level 50): morphism_scope.

MetaCoq Run (to_CCC "id_func_CCC" (fun x : unit => x)).

Print id_func_CCC.

Definition id_func_unquote : unit -> unit -> unit := (id_func_CCC Type_Cat _).

Example id_func_CCC_convertible :
  id_func_unquote = (fun _ => (fun x : unit => x)).
Proof. reflexivity. Qed.


MetaCoq Run (to_CCC "func_applied_CCC" (fun (f : unit -> unit) (x : unit) => f x)).

Print func_applied_CCC.

Definition func_applied_unquote : unit -> (unit -> unit) -> unit -> unit := (func_applied_CCC Type_Cat _).

Example id_func_applied_CCC_convertible :
  func_applied_unquote = fun _ => (fun (f : unit -> unit) (x : unit) => f x).
Proof. reflexivity. Qed.

Example id_func_applied_CCC_convertible1 :
  func_applied_unquote tt  = (fun (f : (unit ⇑ unit)%object) (x : unit) => f x).
Proof. reflexivity. Qed.

Compute (fun f : unit -> unit => (curry (C:=Type_Cat) eval) f).

Example id_func_applied_CCC_convertible2 :
  func_applied_unquote tt  = (curry (C:=Type_Cat) eval).
Proof. reflexivity. Qed.


Set Primitive Projections.

Record my_prod (A B : Type) :=
  { _fst : A;
    _snd : B}.

Arguments _fst {_ _}.
Arguments _snd {_ _}.

Definition swap {A B} (p : my_prod A B) : my_prod B A :=
  Build_my_prod _ _ (_snd p) (_fst p).

Lemma swap_involutive {A B} (p : my_prod A B) : swap (swap p) = p.
Proof. reflexivity. Qed.
