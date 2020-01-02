Require Import MSets OrdSet CustomTactics Eqdep_dec Bool
        FunctionalExtensionality ProofIrrelevance.

(** One usefull lemma to prove properties of permutations *)
Lemma happly {A B : Type} {f g : A -> B} : f = g -> forall x, f x = g x.
Proof.
  intros.
  destruct H. reflexivity.
Qed.


Module Type Atom.
  Declare Module V : SetExtT.
  Axiom eq_dec : forall (a1 a2 : V.elt), {a1 = a2} + {a1 <> a2}.
  Axiom Atom_inf : forall (X : V.t), {x : V.elt | ~ V.In x X}.
End Atom.

Module Nominal (A : Atom).
  Module Atom := A.
  Import A.
  Module SetFacts := WFacts V.
  Module SetProperties := OrdProperties V.

  Notation Atom := Atom.V.elt.
  Notation FinSetA := Atom.V.t.

  Open Scope program_scope.

  Definition is_inj  {A B : Type} (f : A -> B) : Prop :=
    forall (x y : A), f x = f y -> x = y.
  Definition is_surj {A B : Type} (f : A -> B) : Prop :=
    forall (y : B), exists (x : A), f x = y.

  Hint Unfold is_inj is_surj.

  Lemma inj_comp_inj {A B C: Type} (f : A -> B) (g : B -> C) :
    is_inj f -> is_inj g -> (is_inj (g ∘ f)).
  Proof.
    unfold is_inj. intros. auto.
  Qed.

  Lemma surj_comp_surj {A B C: Type} (f : A -> B) (g : B -> C) :
    is_surj f -> is_surj g -> (is_surj (g ∘ f)).
  Proof.
    autounfold. intros H H1 c.
    destruct (H1 c) as [b Hb].
    destruct (H b) as [a Ha].
    exists a; congruence.
  Qed.

  Lemma eq_leibniz_1 x y :  x = y -> V.E.eq x y.
  Proof.
    intros. subst.
    destruct (V.E.eq_equiv).
    apply Equivalence_Reflexive.
  Qed.

  Hint Resolve V.E.eq_leibniz eq_leibniz_1.

  Lemma eq_leibniz_iff x y : V.E.eq x y <-> x=y.
  Proof.
    split;auto.
  Qed.

  (* ----------------------------------- *)
  (* Definition of finitary permutations *)
  (* ----------------------------------- *)

  Definition is_biject {A B} (f : A -> B) :=
    (is_inj f) /\ (is_surj f).

  Definition has_fin_supp f := exists S, (forall t, ~ V.In t S -> f t = t).

  Record Perm :=
    { perm : Atom -> Atom;
      perm_inv : Atom -> Atom;
      l_inv : (perm_inv ∘ perm) = id ;
      r_inv : (perm ∘ perm_inv) = id ;
      fin_supp : has_fin_supp perm}.

  Coercion perm : Perm >-> Funclass.

  Lemma perm_is_biject (p : Perm) : is_biject p.
  Proof.
    destruct p as [p q l r ?].
    simpl. split.
    + intros x y f.
      assert ((q ∘ p) x = (q ∘ p) y) by (unfold compose;now rewrite f).
      rewrite l in H. assumption.
    + intros x. exists (q x). change ((p ∘ q) x = x). now rewrite r.
  Qed.

  Notation "- p" := (perm_inv p).
  
  Lemma perm_eq (p1 p2 : Perm) :
    perm p1 = perm p2 ->
    perm_inv p1 = perm_inv p2 ->
    p1 = p2.
  Proof.
    intros.
    destruct p1 as [f g l r f_s].
    destruct p2 as [f' g' l' r' f_s'].
    simpl in *. subst. f_equal; apply proof_irrelevance.
  Qed.

  Definition id_perm : Perm.
    refine ({| perm:=id; perm_inv := id;
               l_inv := eq_refl; r_inv := eq_refl;
               fin_supp := _|}).
      + exists V.empty;intros;auto.
  Defined.

  Definition perm_comp (p p' : Perm) : Perm.
    refine ({| perm:= (perm p) ∘ (perm p');
               perm_inv := (perm_inv p') ∘ (perm_inv p);
               l_inv := _;
               r_inv := _;
               fin_supp := _ |}).
    + destruct p as [f g l r f_s].
      destruct p' as [f' g' l' r' f_s'].
      simpl.
      change ((g' ∘ (g ∘ f) ∘ f') = id).
      rewrite l.
      change (g' ∘ f' = id).
      rewrite l'. reflexivity.
    + destruct p as [f g l r f_s].
      destruct p' as [f' g' l' r' f_s'].
      simpl.
      change (f ∘ (f' ∘ g') ∘ g = id).
      rewrite r'.
      change (f ∘ g = id).
      rewrite r. reflexivity.
    + destruct p as [f g l r f_s].
      destruct p' as [f' g' l' r' f_s'].
      simpl. destruct f_s as [x Hx]. destruct f_s' as [x' Hx'].
      exists (V.union x x'). intros. unfold compose.
      rewrite Hx';auto with set.
  Defined.

  Notation "p ∘p p'" := (perm_comp p p') (at level 40).

  Lemma perm_comp_assoc p1 p2 p3 :
    (p1 ∘p p2) ∘p p3 = p1 ∘p (p2 ∘p p3).
  Proof.
    apply perm_eq;auto.
  Qed.
  
  (* -------------- *)
  (* Swapping atoms *)
  (* -------------- *)

  (* Swapping two atoms is a simpliest permutation *)
  Definition swap_fn (a b c : V.elt) : V.elt :=
    if (V.E.eq_dec a c) then b
      else (if (V.E.eq_dec b c) then a
        else c).

  Lemma swap_fn_involution {a b} : (swap_fn a b) ∘ (swap_fn a b) = id.
  Proof.
    apply functional_extensionality.
    intros x. unfold compose,swap_fn.
    destruct (V.E.eq_dec a x),( V.E.eq_dec b x),
    (V.E.eq_dec a b),(V.E.eq_dec b b),(V.E.eq_dec a a),(V.E.eq_dec b a);
      rewrite eq_leibniz_iff in *;
      tryfalse;auto;
    destruct (V.E.eq_dec a x),( V.E.eq_dec b x);rewrite eq_leibniz_iff in *;
      tryfalse;auto.
  Qed.

  Hint Unfold swap_fn.

  Lemma id_swap_fn a b c :
    ~ V.In c (V.union (V.singleton a) (V.singleton b)) -> swap_fn a b c = c.
  Proof.
    intros Hc. autounfold.
      destruct (V.E.eq_dec a c); destruct (V.E.eq_dec b c);auto with set;
        exfalso; auto with set.
  Qed.

  Lemma has_fin_supp_swap_fn a b : has_fin_supp (swap_fn a b).
  Proof.
    autounfold.
    exists (V.union (V.singleton a) (V.singleton b)).
    apply id_swap_fn.
  Qed.

  Definition swap (a b : V.elt) : Perm :=
    {| perm := swap_fn a b;
       perm_inv := swap_fn a b;
       l_inv := swap_fn_involution;
       r_inv := swap_fn_involution;
       fin_supp  := has_fin_supp_swap_fn a b|}.

  Lemma is_biject_swap a b : is_biject (swap a b).
  Proof. apply perm_is_biject. Qed.

  Lemma swap_involution a b : (swap a b) ∘p (swap a b) = id_perm.
  Proof.
    apply perm_eq;
      simpl; rewrite swap_fn_involution; reflexivity.
  Qed.
  
  Import ListNotations.

  Fixpoint zip {A B} (xs : list A) (ys : list B) : list (A * B) :=
    match xs, ys with
    | (x::xs'), (y::ys') => (x, y) :: zip xs' ys'
    | _, _ => []
    end.

  (* Swapping bunch of atoms as a composition of primitive swaps *)
  Definition swap_iter_fn (vs : list (Atom * Atom)) : Atom -> Atom :=
    fold_right (fun (e' : (Atom * Atom)) (f : Atom -> Atom) =>
                  let (e1,e2) := e' in f ∘ (swap_fn e1 e2)) id vs.

  (* After we changed the definition of a permutation to contatin the inverse
     permutation it has become trickier to define the iterated permutation 
     TODO : fix prove this and finish the definition of [swap_iter] *)
  (* Lemma swap_iter_fn_involution {xs} : (swap_iter_fn xs) ∘ (swap_iter_fn xs) = id. *)
  (* Proof. *)
  (*   induction xs as [| x]. *)
  (*   - reflexivity. *)
  (*   - simpl. destruct x as [x1 x2]. *)
  (*     change (swap_iter_fn xs ∘ (swap_fn x1 x2 ∘ swap_iter_fn xs) ∘ swap_fn x1 x2 = id). *)

  Hint Resolve inj_comp_inj.

  Lemma swap_iter_fn_inj vs : is_inj (swap_iter_fn vs).
  Proof.
    induction vs;autounfold;intros x y H.
    + auto.
    + destruct a;simpl in *.
      destruct (is_biject_swap e e0).
      assert (is_inj (swap_iter_fn vs ∘ swap_fn e e0));auto.
  Qed.

  Hint Resolve surj_comp_surj.

  Lemma swap_iter_fn_surj vs : is_surj (swap_iter_fn vs).
  Proof.
    induction vs;autounfold;intros x.
    + eexists. reflexivity.
    + destruct a;simpl in *.
      destruct (is_biject_swap e e0).
      assert (is_surj (swap_iter_fn vs ∘ swap_fn e e0));auto.
  Qed.

  Lemma union_not_in A A' e : ~ V.In e (V.union A A') -> ~ V.In e A /\ ~ V.In e A'.
  Proof.
    intros H. auto with set.
  Qed.

  Import SetProperties.

  Hint Resolve P.Dec.F.singleton_1 P.Dec.F.singleton_2 V.E.eq_leibniz : set.

  Lemma is_biject_swap_iter vs vs' : is_biject (swap_iter_fn (zip vs vs')).
  Proof.
    split.
    + apply swap_iter_fn_inj.
    + apply swap_iter_fn_surj.
  Qed.
  
  Lemma has_fin_supp_swap_iter vs vs' :
    has_fin_supp (swap_iter_fn (zip vs vs')).
  Proof.
    exists (V.union (P.of_list vs) (P.of_list vs')). intros.
    generalize dependent vs'.
    induction vs;destruct vs';simpl;auto.
    simpl in *. unfold compose.
    intros H.
    
    (* Needed to apply IH *)
    assert (~ V.In t (V.union (P.of_list vs) (P.of_list vs'))).
    { apply union_not_in in H. destruct H; auto with set. }

    (* Needed to show that swap_n is the identity function outside of support *)
    assert (Ha : t <> a) by (apply union_not_in in H; destruct H; auto with set).
    assert (He : t <> e) by (apply union_not_in in H; destruct H; auto with set).

    assert (Ht : swap_fn a e t = t).
    { apply id_swap_fn. apply union_not_in in H.
      apply P.not_in_union;unfold not; intro Hin.
      * apply Ha; symmetry; auto with set.
      * apply He; symmetry; auto with set. }
    rewrite Ht. auto.
  Qed.

  (* Definition swap_iter (vs vs' : V.t) : Perm := *)
  (*   {| perm := swap_iter_fn (zip (V.elements vs) (V.elements vs')); *)
  (*      is_biject_perm := is_biject_swap_iter _ _; *)
  (*      has_fin_supp_perm := has_fin_supp_swap_iter _ _|}. *)

  Class NomSet :=
    { Carrier : Type;
      action : Perm -> Carrier -> Carrier;
      supp : Carrier -> FinSetA;
      action_id : forall (x : Carrier), action id_perm x = x;
      action_compose : forall (x : Carrier) (p p' : Perm),
          action p (action p' x) = action (p ∘p p') x;
      support_spec : forall  (p : Perm)  (x : Carrier),
          (forall (a : Atom), V.In a (supp x) -> p a = a) ->
          action p x = x}.

  Coercion Carrier : NomSet >-> Sortclass.
  
  Notation "r @ x" := (action r x) (at level 100).


  Definition equivar_fn {X Y : NomSet} (f : X -> Y) :=
    forall x p, f (p @ x) = (p @ (f x)).

  Definition equivar_fn2 {X Y Z : NomSet} (f : X -> Y -> Z) :=
    forall x y p, f (p @ x) (p @ y) = (p @ (f x y)).
  
  Definition equivar_rel {X Y : NomSet} (R : X -> Y -> Prop) :=
    forall (x : X) (y : Y) (p : Perm), R x y -> R (p @ x) (p @ y).
  
  Module NomAtom.

    Instance NomAtom : NomSet.
    refine (
        {| Carrier := Atom;
           action := fun p a => (perm p) a;
           supp := fun a => V.singleton a;
           action_id := fun a => eq_refl _;
           action_compose := fun a p1 p2 => eq_refl;
           support_spec := _
        |}).
    - (* support_spec *) intros. apply H. eauto with set.
    Defined.
  End NomAtom.  
  
  Module PFin.

    Import V.
    
    Hint Resolve V.set_map_spec_1 V.set_map_spec V.set_map_iff : set.

    Instance PFin : NomSet.
    refine ({| Carrier := V.t;
      action := fun p x => V.set_map (perm p) x;
      supp := fun x => x;
      action_id := _;
      action_compose := _;
      support_spec := _|}).
    - (* action_id*)
      intros x. unfold action.
      apply V.set_extensionality. intros x'.
      split.
      + intros Hx. rewrite V.set_map_iff in *. destruct Hx as [y H]. destruct H;subst;auto.
      + intros Hx. eauto with set.
    - (* action_compose *)
      intros x r r'. unfold action. apply V.set_extensionality. intros x'.
        split.
        + intros Hx. rewrite V.set_map_iff in *. destruct Hx.
          intuition;subst;auto. rewrite V.set_map_iff in *.
          destruct H1. intuition. subst.
          exists x1;split;auto.
        + intros Hx. rewrite V.set_map_iff in *. destruct Hx as [x1 H].
          destruct H.
          exists ((perm r') x1). subst; split;auto with set.
    - (* support_spec *)
      intros. unfold action.
      apply set_extensionality. intro y. split.
      + intros H'. auto with set.
        rewrite set_map_iff in *. destruct H' as [y' Hy']. destruct Hy'.
        subst. rewrite H;auto.
      + intros H'. eapply set_map_spec_1;try symmetry;eauto.
    Defined.

    Module Dec := DecidableEqDep BoolDec.

  End PFin.

  
  (* ---------------------------------------------- *)
  (* Freshness conditions and fresh name generators *)
  (* ---------------------------------------------- *)

  Import NomAtom.
  Import PFin.

  Definition fresh {X Y : NomSet} : X -> Y -> Prop :=
    fun (x : X) (y :Y) => V.Disjoint (supp x) (supp y).
  
  Infix "#" := fresh (at level 40).
  
  Import V.

  Lemma disjoint_not_in_1 {X e} : ~ In e X -> Disjoint (singleton e) X.
  Proof.
    intros H.
    apply Disjoint_spec.
    intros. unfold not. intros H1. destruct H1. simpl in *.
    rewrite P.Dec.F.singleton_iff in *.
    rewrite eq_leibniz_iff in *. tryfalse.
  Qed.

  Lemma disjoint_not_in_2 {X e} : Disjoint (singleton e) X -> ~ In e X.
  Proof.
    intros H.
    rewrite Disjoint_spec in *.
    intros. unfold not. intros H1. apply (H e).
    auto with set.
  Qed.

  Lemma disjoint_not_in {X e}: ~ In e X <-> Disjoint (singleton e) X.
  Proof.
    split.
    - apply disjoint_not_in_1.
    - apply disjoint_not_in_2.
  Qed.

  Lemma not_in_set_fresh (a : NomAtom) (A : PFin) : ~ In a A <-> a # A.
  Proof.
    unfold fresh. apply disjoint_not_in.
  Qed.

  (** Type of a function with a property, that generated atom is fresh for the set [a] *)
  Definition FreshFn (a : V.t) := {f : V.t -> NomAtom | forall x, (f x) # a}.

  (** Function that generates a fresh atom using [Atom_inf] property *)
  Definition fresh_fn : forall a, FreshFn a :=
    fun a => let H := Atom.Atom_inf a in
            exist (fun f : t -> NomAtom => forall x : t, ((f x) # a))
                    (fun _ : t => proj1_sig H)
                    (fun _ : t => disjoint_not_in_1 (proj2_sig H)).


    (** Set of fresh atoms (wrt the set [a]) of cardinality [n] *)
  Definition AllFresh a n := { b : V.t | (b # a) /\ V.cardinal b = n }.

  (** Computational part of a function that generates set of fresh atoms *)
  Fixpoint get_freshs_internal (X : V.t) (n : nat) : V.t :=
    match n with
    | O => empty
    | S n' => let fatom := (proj1_sig (fresh_fn X)) X in
              add fatom (get_freshs_internal (add fatom X) n')
    end.

  Lemma get_freshs_internal_all_fresh : forall n a, (get_freshs_internal a n) # a.
  Proof.
    induction n;intros.
    + simpl. compute. apply Disjoint_spec. intros k.
      unfold not. intros H. destruct H as [L R]. rewrite P.Dec.F.empty_iff in *. inversion L.
    + simpl. unfold fresh. rewrite Disjoint_spec. unfold not. intros.
      simpl in *.
      rewrite SetProperties.P.Dec.F.add_iff in *.
      intuition.
      * rewrite eq_leibniz_iff in *. subst. apply (proj2_sig (Atom.Atom_inf a));auto.
      * unfold fresh in *.
        assert (HH := IHn (add (proj1_sig (Atom.Atom_inf a)) a)).
        rewrite Disjoint_spec in *.
        apply (HH k). clear IHn HH. split;auto.
        simpl. rewrite SetProperties.P.Dec.F.add_iff in *. intuition;auto.
  Qed.

  Lemma get_freshs_cardinality : forall n a, V.cardinal (get_freshs_internal a n) = n.
  Proof.
    induction n;intros.
    + simpl. auto with set.
    + simpl. rewrite SetProperties.P.add_cardinal_2;auto.
      remember (proj1_sig (Atom.Atom_inf a)) as b.
      assert (H := get_freshs_internal_all_fresh n (add b a)).
      unfold not. intros. unfold fresh in *.
      rewrite Disjoint_spec in *.
      apply (H b). simpl. rewrite SetProperties.P.Dec.F.add_iff in *.
      split;auto with set.
  Qed.

  (** Function that generates set of fresh atoms along with *)
  (*     the proof of freshness *)
  Definition get_freshs (X : V.t) (n : nat) : AllFresh X n :=
    exist _ (get_freshs_internal X n)
            (conj (get_freshs_internal_all_fresh n X)
                  (get_freshs_cardinality n X)).
  
  Module NomFacts.

    (* An alternative characterisation of support in terms of swap  *)
    Lemma supp_spec_swap {X : NomSet}:
      forall (a b : Atom) (x : X),
        ~ In a (supp x) -> ~ In b (supp x) ->
        ((swap a b) @ x) = x.
    Proof.
      intros a b x Ha Hb.
      apply support_spec.
      intros a' Ha'. simpl. autounfold.
      destruct (SetProperties.P.FM.eq_dec a a');
        destruct (SetProperties.P.FM.eq_dec b a');
        rewrite eq_leibniz_iff in *; congruence.
    Qed.

    Hint Resolve SetProperties.P.Dec.F.singleton_1 SetProperties.P.Dec.F.singleton_2 : set.

    Lemma action_singleton : forall r e, (r @ (singleton e)) = singleton ((perm r) e).
    Proof.
      intros.
      apply set_extensionality.
      intros. unfold action. split.
      + intros H. simpl in *. rewrite V.set_map_iff in *.
        destruct H as [e' He']. destruct He'. subst.
        rewrite SetProperties.P.Dec.F.singleton_iff in *.
        rewrite eq_leibniz_iff in *. subst. reflexivity.
      + intros H. simpl in *. rewrite V.set_map_iff in *.
        rewrite SetProperties.P.Dec.F.singleton_iff in *.
        rewrite eq_leibniz_iff in H. subst.
        exists e;auto with set.
    Qed.

    Lemma equivar_union : equivar_fn2 union.
    Proof.
      unfold equivar_fn2.
      intros x y p.
      apply V.set_extensionality.
      intros z. split.
      + intros H. unfold action in *. rewrite union_spec in *.
        simpl in *. rewrite set_map_iff in *.
        destruct H.
        * destruct H. exists x0; destruct H; split; auto with set.
        * rewrite set_map_iff in *. destruct H as [x0 Hx0]. destruct Hx0.
          exists x0;split;auto. rewrite union_spec in *. auto.
      + intros H. unfold action in *. rewrite union_spec in *.
        simpl in *. rewrite set_map_iff in *.
        destruct H. destruct H; subst.
        rewrite union_spec in *.
        destruct H0;auto with set.
        left. exists x0;auto.
    Qed.
    
    Lemma equivar_inter : equivar_fn2 inter.
    Proof.
      intros x y p.
      apply V.set_extensionality.
      intros z. split.      
      + intros H. unfold action in *. simpl in *.
        rewrite inter_spec in *. rewrite set_map_iff in *.
        destruct H as [He' Hz]. destruct He' as [e' Htl].
        destruct Htl; subst.
        rewrite set_map_iff in *.
        destruct Hz as [e'' Htl]. destruct Htl.
        exists e''.
        destruct p as [f g l r Hsupp]. simpl in *.
        assert (Heq : e' = e'') by
            (replace (e') with (g (f e')) by apply (happly l);
             replace (e'') with (g (f e'')) by apply (happly l);
             congruence).
        subst. auto with set.
      + intros H. unfold action in *.
        simpl in *. rewrite set_map_iff in *.
        destruct H. destruct H; subst.
        rewrite inter_spec in *.
        destruct H0;auto with set.
    Qed.

    Lemma equivar_fresh_set : equivar_rel (fun (x y : PFin) => x # y). 
    Proof.
      unfold equivar_rel.
      intros x y p. destruct p as [f g l r Hsupp].
      intros. rewrite Disjoint_spec in *. intros k.
      unfold action in *. simpl. intros H1. rewrite set_map_iff in *.
      destruct H1. destruct H0. destruct H0. subst.
      apply (H x0). split;auto.
      rewrite set_map_iff in *.
      destruct H1. destruct H0.
      (* NOTE : here we use the property that permutation is injective.
         We prove injectivity using the left inverse property*)
      assert (x0 = x1) by
            (replace (x0) with (g (f x0)) by apply (happly l);
             replace (x1) with (g (f x1)) by apply (happly l);
             congruence).
      subst;auto.
    Qed.

  End NomFacts.

  Lemma swap_fresh {X : NomSet} {a b : NomAtom} {x : X} :
  a # x -> b # x -> ((swap a b) @ x) = x.
  Proof.
    intros Ha Hb.
    apply NomFacts.supp_spec_swap;
    apply not_in_set_fresh; auto.
  Qed.

End Nominal.
