Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope list.

(* claim forall type A, x,y of A, it holds that {x=y} + {x<>y}. *)
Axiom eq_dec: forall {A: Type} (x y: A), {x = y} + {x <> y}.


Theorem equiv_in_domain:
  forall {A B: Type} (f: A -> B) (R: B -> B -> Prop),
    Equivalence R ->
    Equivalence (fun a1 a2 => R (f a1) (f a2)).
Proof.
  intros.
  split.
  + unfold Reflexive.
    intros.
    reflexivity.
  + unfold Symmetric.
    intros.
    symmetry; tauto.
  + unfold Transitive.
    intros.
    transitivity (f y); tauto.
Qed.

Lemma Forall2_to_forall_r:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f l1 l2 ->
    (forall b, In b l2 -> exists a, In a l1 /\ f a b).
Proof.
  intros.
  induction H.
  - inversion H0.
  - destruct H0.
    + subst.
      exists x.
      split; auto.
      left; auto.
    + apply IHForall2 in H0.
      destruct H0 as [a [? ?]].
      exists a.
      split; auto.
      right; auto.
Qed.

Lemma Forall2_to_forall_l:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f l1 l2 ->
    (forall a, In a l1 -> exists b, In b l2 /\ f a b).
Proof.
  intros.
  induction H.
  - inversion H0.
  - destruct H0.
    + subst.
      exists y.
      split; auto.
      left; auto.
    + apply IHForall2 in H0.
      destruct H0 as [b [? ?]].
      exists b.
      split; auto.
      right; auto.
Qed.

Lemma Forall2_perm_l_exists:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop) (l1': list A),
    Permutation l1 l1' ->
    Forall2 f l1 l2 ->
    exists l2', Permutation l2 l2' /\ Forall2 f l1' l2'.
Proof.
Admitted.

(*********************************************************)
(**                                                      *)
(** General Definition of Monad                          *)
(**                                                      *)
(*********************************************************)

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Import Monad.

Module MonadNotation.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1 (fun _: unit => e2))
  (at level 61, right associativity) : monad_scope.

End MonadNotation.

Arguments bind: simpl never.
Arguments ret: simpl never.
Import MonadNotation.
Local Open Scope monad.

(*********************************************************)
(**                                                      *)
(** Set Monad                                            *)
(**                                                      *)
(*********************************************************)

Module SetMonad.

Definition M (A: Type): Type := A -> Prop.

Definition bind: forall (A B: Type) (f: M A) (g: A -> M B), M B :=
  fun (A B: Type) (f: M A) (g: A -> M B) =>
    fun b: B => exists a: A, a ∈ f /\ b ∈ g a.

Definition ret: forall (A: Type) (a: A), M A :=
  fun (A: Type) (a: A) => eq a.

End SetMonad.

#[export] Instance set_monad: Monad SetMonad.M := {|
  bind := SetMonad.bind;
  ret := SetMonad.ret;
|}.

Definition Hoare {A: Type} (c: SetMonad.M A) (P: A -> Prop): Prop :=
  forall a, a ∈ c -> P a.


  Theorem Hoare_bind {A B: Type}:
  forall (f: SetMonad.M A)
         (g: A -> SetMonad.M B)
         (P: A -> Prop)
         (Q: B -> Prop),
    Hoare f P ->
    (forall a, P a -> Hoare (g a) Q) ->
    Hoare (bind f g) Q.
Proof.
  intros.
  unfold Hoare; sets_unfold;
  unfold bind, set_monad, SetMonad.bind.
  intros b [a [? ?]].
  specialize (H _ H1).
  specialize (H0 _ H _ H2).
  tauto.
Qed.

Theorem Hoare_ret {A: Type}:
  forall (a: A) (P: A -> Prop),
    P a -> Hoare (ret a) P.
Proof.
  intros.
  unfold Hoare, ret, set_monad, SetMonad.ret; sets_unfold.
  intros.
  rewrite <- H0; tauto.
Qed.

Theorem Hoare_conseq {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    (forall a, P a -> Q a) ->
    Hoare f P ->
    Hoare f Q.
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.

Theorem Hoare_conjunct {A: Type}:
  forall (f: SetMonad.M A) (P Q: A -> Prop),
    Hoare f P ->
    Hoare f Q ->
    Hoare f (fun a => P a /\ Q a).
Proof.
  unfold Hoare; intros.
  specialize (H a).
  specialize (H0 a).
  tauto.
Qed.



#[export] Instance SetMonad_bind_congr (A B: Type):
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv)
    (@bind _ set_monad A B).
Proof.
  unfold Proper, respectful.
  unfold set_monad, bind, SetMonad.bind;
  sets_unfold; intros f1 f2 Hf g1 g2 Hg.
  intros b; split; intros [a ?]; exists a.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
  + specialize (Hf a); specialize (Hg a b).
    tauto.
Qed.

#[export] Instance Hoare_congr {A: Type}:
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare A).
Proof.
  unfold Proper, respectful.
  intros; unfold Hoare.
  subst.
  split; intros.
  + rewrite <- H in H1.
    apply (H0 a); tauto.
  + rewrite H in H1.
    apply (H0 a); tauto.
Qed.

(*********************************************************)
(**                                                      *)
(** List Operation                                       *)
(**                                                      *)
(*********************************************************)


(* use ListSet to define *)

Definition filter_dup {A: Type} (l: list A): list A :=
  fold_right (fun a: A => fun s: set A => set_add eq_dec a s) (empty_set A) l.

(* Lemmas and Theorems about filter_dup *)

Lemma filter_dup_nodup {A: Type}:
  forall (l: list A),
    NoDup (filter_dup l).
Proof.
  intros.
  induction l as [| a l IH].
  - simpl.
    constructor.
  - simpl.
    apply set_add_nodup.
    auto.
Qed.

Lemma filter_dup_incl {A: Type}:
  forall (l: list A),
    forall x, In x l <-> In x (filter_dup l).
Proof.
  intros.
  induction l as [| a l IH].
  - simpl.
    split; intros.
    + inversion H.
    + inversion H.
  - destruct (eq_dec x a).
    + subst.
      simpl.
      split; intros.
      * destruct H.
        {
          apply set_add_intro2.
          reflexivity.
        }
        {
          apply set_add_intro1.
          apply IH.
          auto.
        }
      * apply set_add_elim in H.
        destruct H.
        {
          auto.
        }
        {
          right.
          apply IH.
          auto.
        }
    + simpl.
      split; intros.
      * destruct H.
        {
          subst; absurd (x<>x); auto.
        }
        {
          apply set_add_intro1.
          apply IH.
          auto.
        }
      * apply set_add_elim in H.
        destruct H.
        {
          subst.
          absurd (a<>a); auto.
        }
        {
          right.
          apply IH.
          auto.
        }
Qed.

Lemma Permutation_filter_dup_filter_dup_incl_inv:
  forall {A: Type} (l1 l2: list A),
    (forall x, In x l1 <-> In x l2) ->
    Permutation (filter_dup l1) (filter_dup l2).
Proof.
  intros.
  apply NoDup_Permutation.
  - apply filter_dup_nodup.
  - apply filter_dup_nodup.
  - intros.
    specialize (filter_dup_incl l1 x).
    specialize (filter_dup_incl l2 x).
    specialize (H x).
    tauto.
Qed.

Lemma filter_dup_in {A: Type}:
  forall (l: list A),
    forall x, In x (filter_dup l) -> In x l.
Proof.
  intros.
  apply filter_dup_incl.
  auto.
Qed.

Lemma filter_dup_in_inv {A: Type}:
  forall (l: list A),
    forall x, In x l -> In x (filter_dup l).
Proof.
  intros.
  specialize (filter_dup_incl l x).
  tauto.
Qed.

Lemma filter_dup_in_iff {A: Type}:
  forall (l: list A),
    forall x, In x l <-> In x (filter_dup l).
Proof.
  intros.
  split; intros.
  - apply filter_dup_in_inv.
    auto.
  - apply filter_dup_in.
    auto.
Qed.

Lemma filter_dup_incl_list{A: Type}:
  forall (lx l: list A),
    incl lx l ->
    incl lx (filter_dup l).
Proof.
  intros.
  unfold incl in *.
  intros.
  apply filter_dup_in_inv.
  apply H.
  auto.
Qed.

Lemma filter_dup_incl_list_inv{A: Type}:
  forall (lx l: list A),
    incl lx (filter_dup l) ->
    incl lx l.
Proof.
  intros.
  unfold incl in *.
  intros.
  apply filter_dup_in.
  apply H.
  auto.
Qed.

Lemma Permutation_notin {A: Type}:
  forall {l1 l2: list A} {x: A},
    Permutation l1 l2 ->
    ~ In x l1 ->
    ~ In x l2.
Proof.
  intros.
  intro.
  apply H0.
  symmetry in H.
  pose proof Permutation_in _ H H1.
  tauto.
Qed.

Lemma in_set_add_app {A: Type}:
  forall (l: list A) (x: A),
    In x l ->
    set_add eq_dec x l = l.
Proof.
  intros.
  induction l as [| a l IH].
  - simpl.
    destruct H.
  - simpl.
    destruct (eq_dec x a).
    + subst.
      simpl.
      reflexivity.
    + destruct H.
      * subst.
        absurd (x<>x); auto.
      * specialize (IH H).
        rewrite IH.
        reflexivity.
Qed. 

Lemma notin_set_add_app {A: Type}:
  forall (l: list A) (x: A),
    ~ In x l ->
    set_add eq_dec x l = l ++ [x].
Proof.
  intros.
  induction l as [| a l IH].
  - simpl.
    destruct (eq_dec x x).
    + reflexivity.
    + contradiction.
  - simpl.
    destruct (eq_dec x a).
    + subst.
      destruct H.
      simpl; left; auto.
    + pose proof not_in_cons x a l as [H1 _].
      specialize (H1 H).
      destruct H1 as [H1 H2].
      specialize (IH H2).
      rewrite IH.
      reflexivity.
Qed.

Lemma perm_filter_dup_cons {A: Type}:
  forall (l l1 l2: list A),
    Permutation (filter_dup l1) (filter_dup l2) ->
    Permutation (filter_dup (l ++ l1)) (filter_dup (l ++ l2)).
Proof.
  intros.
  induction l as [| a l IH].
  - simpl.
    auto.
  - rewrite <- app_comm_cons.
    rewrite <- app_comm_cons.
    simpl.
    destruct (in_dec eq_dec a (filter_dup (l ++ l1))).
    + pose proof Permutation_in _ IH i.
      pose proof in_set_add_app (filter_dup (l ++ l1)) a i.
      pose proof in_set_add_app (filter_dup (l ++ l2)) a H0.
      rewrite H1.
      rewrite H2.
      exact IH.
    + pose proof Permutation_notin IH n.
      pose proof notin_set_add_app (filter_dup (l ++ l1)) a n.
      pose proof notin_set_add_app (filter_dup (l ++ l2)) a H0.
      rewrite H1.
      rewrite H2.
      (* Search (Permutation (_ ++ _) (_ ++ _)). *)
      apply Permutation_app_tail.
      exact IH.
Qed.

Lemma perm_filter_dup_incl{A: Type}:
  forall (l1 l2: list A),
    (forall x, In x l1 <-> In x l2 ) ->
              Permutation (filter_dup l1) (filter_dup l2).
Proof.
  (* Search (Permutation). *)
  intros.
  apply NoDup_Permutation.
  - apply filter_dup_nodup.
  - apply filter_dup_nodup.
  - intros.
    pose proof filter_dup_incl l1 x.
    pose proof filter_dup_incl l2 x.
    specialize (H x).
    tauto.
Qed.

Lemma nodup_perm_filter_dup {A: Type}:
  forall (l: list A),
    NoDup l ->
    Permutation l (filter_dup l).
Proof.
  intros.
  induction H.
  - simpl.
    constructor.
  - simpl.
    assert (~ In x (filter_dup l)). {
      pose proof Permutation_notin IHNoDup H.
      tauto.
    }
    pose proof notin_set_add_app (filter_dup l) x H1.
    rewrite H2.
    (* Search Permutation. *)
    rewrite Permutation_app_comm.
    simpl.
    apply perm_skip.
    apply IHNoDup.
Qed.

Lemma perm_filter_dup_nodup {A: Type}:
  forall (l1 l2: list A),
    Permutation l1 (filter_dup l2) ->
    NoDup l1.
Proof.
  intros.
  pose proof filter_dup_nodup l2.
  (* Search (Permutation). *)
  pose proof Permutation_NoDup' H.
  tauto.
Qed.

Lemma nodup_app_l {A: Type}:
  forall (l1 l2: list A),
    NoDup (l1 ++ l2) ->
    NoDup l1.
Proof.
  intros.
  induction l1 as [| a l1 IH].
  - constructor.
  - inversion H.
    constructor.
    + intro.
      specialize (IH H3).
      subst.
      (* Search (In _ (_ ++ _)). *)
      assert (In a (l1 ++ l2)) by (apply in_or_app; auto).
      contradiction.
    + subst.
      auto.
Qed.

Lemma nodup_app_r {A: Type}:
  forall (l1 l2: list A),
    NoDup (l1 ++ l2) ->
    NoDup l2.
Proof.
  intros.
  induction l1 as [| a l1 IH].
  - auto.
  - inversion H.
    apply IH.
    auto.
Qed.

Lemma perm_nodup_app_l {A: Type}:
  forall (l1 l2 l3: list A),
    Permutation (l1 ++ l2) l3 ->
    NoDup l3 ->
    NoDup l1.
Proof.
  intros.
  (* Search Permutation. *)
  apply Permutation_sym in H.
  pose proof Permutation_NoDup H H0.
  (* Search (NoDup (_ ++ _)). *)
  apply nodup_app_l in H1.
  tauto.
Qed.

Lemma perm_nodup_app_r {A: Type}:
  forall (l1 l2 l3: list A),
    Permutation (l1 ++ l2) l3 ->
    NoDup l3 ->
    NoDup l2.
Proof.
  intros.
  apply Permutation_sym in H.
  pose proof Permutation_NoDup H H0.
  apply nodup_app_r in H1.
  tauto.
Qed.

Lemma in_listlist_concat_incl {A: Type}:
  forall (l: list A) (ll: list (list A)),
    In l ll ->
    incl l (concat ll).
Proof.
  intros.
  unfold incl.
  intros.
  apply in_concat.
  exists l.
  split; auto.
Qed.

Definition perm_after_map {A B: Type} (f: A -> B) (l1 l2: list A): Prop :=
  Permutation (map f l1) (map f l2).

#[export] Instance eq_perm_after_map {A B: Type} (f: A -> B):
  Equivalence (@perm_after_map A B f).
Proof.
  unfold perm_after_map.
  apply equiv_in_domain.
  split.
  - unfold Reflexive.
    reflexivity.
  - unfold Symmetric.
    symmetry.
    auto.
  - unfold Transitive.
    intros.
    transitivity y.
    all: auto.
Qed.

Lemma perm_after_map_perm {A B: Type}:
  forall (f: A -> B) (l1 l2 l3 l4: list A),
    Permutation l1 l2 ->
    Permutation l3 l4 ->
    perm_after_map f l1 l3 ->
    perm_after_map f l2 l4.
Proof.
  intros.
  unfold perm_after_map in *.
  (* Search (Permutation). *)
  pose proof Permutation_map f H as H2.
  pose proof Permutation_map f H0 as H3.
  rewrite <- H2.
  rewrite <- H3.
  auto.
Qed.

(* make the above into congr instance *)
#[export] Instance perm_after_map_congr {A B: Type} (f: A -> B):
  Proper (Permutation (A:=A) ==> Permutation (A:=A) ==> iff) (perm_after_map f).
Proof.
  unfold Proper, respectful.
  intros.
  split; intros.
  - apply perm_after_map_perm with (l1 := x) (l3 := x0); auto.
  - apply perm_after_map_perm with (l1 := y) (l3 := y0); auto.
    all: symmetry; auto.
Qed.

Lemma Forall2_same_length {A B: Type}:
  forall (P: A -> B -> Prop) l1 l2,
    Forall2 P l1 l2 ->
    length l1 = length l2.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl.
    rewrite IHForall2.
    reflexivity.
Qed.

Lemma Forall2_in_r_exists:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f l1 l2 ->
    forall b, In b l2 -> exists a, In a l1 /\ f a b.
Proof.
  intros.
  induction H.
  - inversion H0.
  - destruct H0.
    + subst.
      exists x.
      split; auto.
      left; auto.
    + apply IHForall2 in H0.
      destruct H0 as [a [? ?]].
      exists a.
      split; auto.
      right; auto.
Qed.

Lemma Forall2_in_l_exists:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f l1 l2 ->
    forall a, In a l1 -> exists b, In b l2 /\ f a b.
Proof.
  intros.
  induction H.
  - inversion H0.
  - destruct H0.
    + subst.
      exists y.
      split; auto.
      left; auto.
    + apply IHForall2 in H0.
      destruct H0 as [b [? ?]].
      exists b.
      split; auto.
      right; auto.
Qed.

Lemma Forall2_pair_Forall2_lt_length {A B1 B2: Type}:
  forall n,
  forall
    (P1: A -> B1 -> Prop)
    (P2: A -> B2 -> Prop)
    (Q: B1 -> B2 -> Prop) 
    la lb1 lb2,
    length la < n ->
    Forall2 P1 la lb1 ->
    Forall2 P2 la lb2 ->
    ( forall a b1 b2,
      In a la ->
      In b1 lb1 ->
      In b2 lb2 ->
      P1 a b1 ->
      P2 a b2 ->
      Q b1 b2 ) ->
    Forall2 Q lb1 lb2.
Proof.
  assert (
    forall n,
    forall
      (P1: A -> B1 -> Prop)
      (P2: A -> B2 -> Prop)
      (Q: B1 -> B2 -> Prop) 
      la lb1 lb2,
      length la <= n ->
      Forall2 P1 la lb1 ->
      Forall2 P2 la lb2 ->
      ( forall a b1 b2,
        In a la ->
        In b1 lb1 ->
        In b2 lb2 ->
        P1 a b1 ->
        P2 a b2 ->
        Q b1 b2 ) ->
      Forall2 Q lb1 lb2
  ) as H_ind. {
    induction n as [| n IH].
    - intros.
      inversion H.
      pose proof length_zero_iff_nil la as [H_la_nil _]; specialize (H_la_nil H4).
      pose proof Forall2_same_length _ _ _ H0.
      pose proof Forall2_same_length _ _ _ H1.
      subst; simpl in *.
      assert (lb1 = []) by (apply length_zero_iff_nil; auto).
      assert (lb2 = []) by (apply length_zero_iff_nil; auto).
      subst; simpl in *.
      constructor.
    - intros.
      inversion H0.
      {
        subst.
        inversion H1.
        subst.
        constructor.
      }
      inversion H1.
      {
        subst.
        inversion H7.
      }
      constructor.
      {
        apply H2 with (a := x).
        all: auto.
        all: subst; simpl in *; auto.
        inversion H9.
        rewrite <- H6.
        auto.
      }
      remember l as la'; subst l.
      remember l' as lb1'; subst l'.
      remember l'0 as lb2'; subst l'0.
      specialize (IH P1 P2 Q).
      rewrite <- H5 in H9.
      injection H9 as H9.
      specialize (IH la' lb1' lb2').
      assert (length la' <= n) as Hlength. {
        subst la.
        simpl in H.
        lia.
      }
      apply IH; auto.
      * subst.
        auto.
      * intros.
        subst.
        pose proof (H2 a b1 b2).
        (* Search (In _ (_ :: _)). *)
        pose proof in_cons x _ _ H12.
        pose proof in_cons y _ _ H13.
        pose proof in_cons y0 _ _ H14.
        auto.
  }
  intros n.
  intros.
  assert (length la <= n) as Hlength. {
    lia.
  }
  specialize (H_ind n P1 P2 Q la lb1 lb2 Hlength H0 H1 H2).
  auto.
Qed.

Lemma Forall2_pair_Forall2 {A B: Type}:
  forall (P: A -> B -> Prop) (Q: B -> B -> Prop) l la lb,
    Forall2 P l la ->
    Forall2 P l lb ->
    ( forall a b1 b2,
      In a l ->
      In b1 la ->
      In b2 lb ->
      P a b1 ->
      P a b2 ->
      Q b1 b2 ) ->
    Forall2 Q la lb.

Proof.
  intros P Q l.
  pose proof Forall2_pair_Forall2_lt_length (S (length l)) P P Q l.
  intros.
  assert (length l < S (length l)) by lia.
  eapply H.
  all: auto.
Qed.

Lemma In_concat_map_exists {A B: Type}:
  forall (l: list A) (f: A -> list B) (b: B),
    In b (concat (map f l)) ->
    exists a, In a l /\ In b (f a).
Proof.
  intros.
  apply in_concat in H.
  destruct H as [l' [? ?]].
  apply in_map_iff in H.
  destruct H as [a [? ?]].
  subst.
  exists a.
  auto.
Qed.

Lemma In_in_concat_map {A B: Type}:
  forall (l: list A) (f: A -> list B) (b: B),
    (exists a, In a l /\ In b (f a)) ->
    In b (concat (map f l)).
Proof.
  intros.
  destruct H as [a [? ?]].
  apply in_concat.
  exists (f a).
  split; auto.
  apply in_map_iff.
  exists a.
  auto.
Qed.

Lemma in_in_app_app:
  forall {A: Type} (a: A) (l1 l2 l0: list A),
    (
      In a l1 -> In a l2
    ) ->
    (
      In a (l0 ++ l1) -> In a (l0 ++ l2)
    ).
Proof.
  intros.
  - apply in_app_or in H0.
    apply in_or_app.
    destruct H0.
    + left. auto.
    + right. apply H. auto.
Qed.


Lemma Rge_ne_gt:
  forall r1 r2,
    (r1 >= r2)%R ->
    r1 <> r2 ->
    (r1 > r2)%R.
Proof.
  intros.
  destruct (Rgt_ge_dec r1 r2).
  - auto.
  - pose proof Rge_le r1 r2 H.
    pose proof Rge_antisym _ _ H r.
    contradiction.
Qed.

(*********************************************************)
(**                                                      *)
(** Probability Distribution                             *)
(**                                                      *)
(*********************************************************)

Definition sum (l: list R): R :=
  fold_right Rplus 0%R l.

Definition sum_prob {A: Type} (pset: list A) (prob: A -> R): R :=
  sum (map prob pset).

Lemma sum_app:
  forall (l1 l2: list R),
    sum (l1 ++ l2) = (sum l1 + sum l2)%R.
Proof.
  intros.
  induction l1.
  - simpl.
    lra.
  - simpl.
    rewrite IHl1.
    lra.
Qed.

Lemma sum_map_add:
  forall {A: Type},
  forall (l: list A),
    forall (f f1 f2: A -> R),
    (forall a, f a = f1 a + f2 a)%R ->
    (sum (map f l) = sum (map f1 l) + sum (map f2 l))%R.
Proof.
  intros.
  induction l.
  - simpl.
    rewrite Rplus_0_r.
    reflexivity.
  - simpl.
    rewrite IHl.
    rewrite H.
    lra.
Qed.

Lemma sum_map_sum_map:
  forall (A B: Type) (la: list A) (lb: list B) (g: B -> A -> R),
    sum (
      map (fun a => 
                sum (
                  map (fun b => (g b) a) 
                  lb)
          )
      la
    )
    =
    sum (
      map (fun b =>
                sum (
                  map (fun a => (g b) a) 
                  la)
          )
      lb
    ).
Proof.
  intros.
  induction la as [| a la IHa], lb as [| b lb].
  - simpl.
    reflexivity.
  - simpl.
    enough (sum (map (fun _ : B => 0) lb) = 0)%R.
    {
      rewrite H.
      rewrite Rplus_0_r; reflexivity.
    }
    induction lb.
    + simpl; reflexivity.
    + simpl; rewrite IHlb; rewrite Rplus_0_r; reflexivity.
  - simpl.
    enough (sum (map (fun _ : A => 0) la) = 0)%R.
    {
      rewrite H.
      rewrite Rplus_0_r; reflexivity.
    }
    simpl in IHa.
    assumption.
  - simpl in *.

    (* Search (?x + _ = ?x + _)%R. *)
    (* SearchRewrite ((_ + _)+_)%R. *)
    rewrite Rplus_assoc.
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    rewrite IHa.
    rewrite Rplus_comm.
    rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    pose proof sum_map_add lb.
    assert (
      forall b: B,
      (fun b0 : B => (g b0 a + sum (map (fun a0 : A => g b0 a0) la))%R) b =
      (fun b0 : B => (sum (map (fun a0 : A => g b0 a0) la))%R) b
      +
      (fun b0 : B => (g b0 a)%R) b
    )%R. {
      intros.
      lra.
    }
    specialize (H _ _ _ H0).
    rewrite H.
    reflexivity.
Qed.

Lemma sum_map_multi:
  forall {A: Type} (l: list A) (f: A -> R) (r: R),
    sum (map (fun a => r * f a) l)%R = (r * sum (map f l))%R.
Proof.
  intros.
  induction l.
  - simpl.
    lra.
  - simpl.
    rewrite IHl.
    lra.
Qed.

Module ProbDistr.

Record Distr (A: Type): Type := {
  prob: A -> R;
  pset: list A;
}.

Arguments prob {_} _.
Arguments pset {_} _.

Record legal {A: Type} (d: Distr A): Prop := {
  legal_no_dup: NoDup d.(pset);
  legal_nonneg: forall a, (d.(prob) a >= 0)%R;
  legal_pset_valid: forall a, (d.(prob) a > 0)%R -> In a d.(pset);
  legal_prob_1: sum_prob d.(pset) d.(prob) = 1%R;
  (* legal_pset_pos: forall a, In a d.(pset) -> (d.(prob) a > 0)%R; *)
}.

Definition equiv {A: Type} (d1 d2: Distr A): Prop :=
  (forall a: A, d1.(prob) a = d2.(prob) a) /\
  Permutation d1.(pset) d2.(pset).


Definition is_det {A: Type} (a: A) (d: Distr A): Prop :=
  d.(pset) = [a] /\ d.(prob) a = 1%R /\
  forall b, (a <> b) -> d.(prob) b = 0%R.

(** This definition should only be used when ds contains
    positive probabilities. *)
Record sum_distr {A: Type}
                 (ds: list (R * Distr A))
                 (d0: Distr A): Prop :=
{
  sum_pset_valid:
    (* forall a, In a d0.(pset) <->
              In a (concat (map (fun '(r, d) => d.(pset)) ds)); *)
    Permutation
        d0.(pset)
      (
        filter_dup
        (concat (map (fun '(r, d) => d.(pset)) ds))
      );

  sum_prob_valid:
    forall a, d0.(prob) a =
              sum (map (fun '(r, d) => r * d.(prob) a) ds)%R;
}.

Definition compute_pr (d: Distr Prop) (r: R): Prop :=
  exists (l: list Prop),
    (forall P, In P l <-> In P d.(pset) /\ P) /\
    (sum_prob l d.(prob) = r) /\
    NoDup l.

Definition imply_event (d1 d2: Distr Prop): Prop :=
  exists r1 r2,
    compute_pr d1 r1 /\
    compute_pr d2 r2 /\
    (r1 <= r2)%R.

Definition equiv_event (d1 d2: Distr Prop): Prop :=
  exists r1 r2,
    compute_pr d1 r1 /\
    compute_pr d2 r2 /\
    (r1 = r2)%R.

End ProbDistr.

Notation "'Distr'" := (ProbDistr.Distr) (at level 0).
Notation "x '.(pset)'" := (ProbDistr.pset x) (at level 1).
Notation "x '.(prob)'" := (ProbDistr.prob x) (at level 1).
Notation "x '.(legal_no_dup)'" := (ProbDistr.legal_no_dup _ x) (at level 1).
Notation "x '.(legal_nonneg)'" := (ProbDistr.legal_nonneg _ x) (at level 1).
Notation "x '.(legal_pset_valid)'" := (ProbDistr.legal_pset_valid _ x) (at level 1).
Notation "x '.(legal_prob_1)'" := (ProbDistr.legal_prob_1 _ x) (at level 1).

(* Lemmas *)

Lemma sum_distr_exists:
  forall {A: Type} (ds: list (R * Distr A)),
    exists d0, ProbDistr.sum_distr ds d0.
Proof.
  intros.
  exists {| ProbDistr.prob := fun a => sum (map (fun '(r, d) => r * d.(prob) a) ds)%R;
            ProbDistr.pset := filter_dup (concat (map (fun '(r, d) => d.(pset)) ds)) |}.
  split.
  - simpl.
    reflexivity.
  - intros.
    simpl.
    reflexivity.
Qed.

(* Forall2
               (fun '(r1, d1) '(r2, d2) =>
                r1 = r2 /\ ProbDistr.equiv d1 d2) 
  l1 l2 
  holds, then sum_distr l1 ?d0 -> sum_distr l2 ?d0  
  make it a proper instance *)              
(* Lemma sum_distr_congr {A: Type}:
  Proper (Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) ==> ProbDistr.equiv ==> iff) (@ProbDistr.sum_distr A).
Proof.
  unfold Proper, respectful.
  intros l1 l2 Hl r1 r2 ?.
  split; intros.
  - destruct H0 as [Hpset Hprob]. *)
(* Admitted. *)

Lemma sum_distr_congr {A: Type}:
  forall (l1 l2: list (R * Distr A)) (d0: Distr A),
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) l1 l2 ->
    ProbDistr.sum_distr l1 d0 <->
    ProbDistr.sum_distr l2 d0.
Proof.
Admitted.

Lemma sum_distr_congr_1 {A: Type}:
  forall (l1 l2: list (R * Distr A)) (d0: Distr A),
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) l1 l2 ->
    ProbDistr.sum_distr l1 d0 ->
    ProbDistr.sum_distr l2 d0.
Proof.
Admitted.

Lemma sum_distr_congr_2 {A: Type}:
  forall (l1 l2: list (R * Distr A)) (d0: Distr A),
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) l1 l2 ->
    ProbDistr.sum_distr l2 d0 ->
    ProbDistr.sum_distr l1 d0.
Proof.
Admitted.


(* permutation of ds is ok with sum_distr *)
(* export as congr instance *)
#[export] Instance sum_distr_perm {A: Type}:
  Proper (Permutation (A:=(R * Distr A)) ==> eq ==> iff) (@ProbDistr.sum_distr A).
Proof.
  unfold Proper, respectful.
  intros.
Admitted.


Lemma incl_nodup_perm:
  forall {A: Type} (l1 l2: list A),
    NoDup l1 ->
    NoDup l2 ->
    incl l1 l2 ->
    incl l2 l1 ->
    Permutation l1 l2.
Proof.
  intros.
  apply NoDup_Permutation; auto.
  intros.
  unfold incl in *.
  split; intros.
  - auto.
  - auto.
Qed.

Lemma list_partition_in_notin:
  forall {A: Type} (l t: list A),
    exists t1 t2,
      Permutation (t1 ++ t2) t /\
      (forall a, In a t1 -> In a l) /\
      (forall a, In a t2 -> ~ In a l).
Proof.
  intros.
  exists (filter (fun a => if in_dec eq_dec a l then true else false) t),
         (filter (fun a => if in_dec eq_dec a l then false else true) t).
  split.
  - induction t.
    + simpl.
      reflexivity.
    + simpl.
      destruct (in_dec eq_dec a l).
      * simpl.
        rewrite IHt.
        reflexivity.
      * simpl.
        (* Search (Permutation (_ ++ _)). *)
        rewrite Permutation_app_comm.
        simpl.
        apply Permutation_cons; [reflexivity | auto].
        rewrite Permutation_app_comm.
        apply IHt.
  - split; intros.
    + apply filter_In in H.
      destruct H.
      destruct (in_dec eq_dec a l).
      * auto.
      * inversion H0.
    + apply filter_In in H.
      destruct H.
      destruct (in_dec eq_dec a l).
      * inversion H0.
      * auto.
Qed.




#[export] Instance sum_congr :
  Proper (Permutation (A:=R) ==> eq) (sum).
Proof.
  unfold Proper, respectful.
  intros l1 l2 H.
  induction H.
  - reflexivity.
  - simpl.
    f_equal.
    assumption.
  - simpl.
    rewrite Rplus_comm.
    rewrite Rplus_assoc.
    f_equal.
    rewrite Rplus_comm.
    reflexivity.
  - transitivity (sum l'); assumption.
Qed.

Lemma perm_map:
  forall (A B: Type) (f: A -> B) (l1 l2: list A),
    Permutation l1 l2 ->
    Permutation (map f l1) (map f l2).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl.
    constructor.
    assumption.
  - simpl.
    constructor.
  - apply Permutation_trans with (l' := map f l'); assumption.
Qed.

Definition eq_fun {A B: Type} (f1 f2: A -> B): Prop :=
  forall a, f1 a = f2 a.

#[export] Instance sum_prob_congr {A: Type}:
  Proper (Permutation (A:=A) ==> eq_fun ==> eq) (@sum_prob A).
Proof.
  unfold Proper, respectful.
  intros l1 l2 Hl r1 r2 ?.
  unfold eq_fun in H.
  unfold sum_prob.
  rewrite Hl. 
  apply sum_congr.
  induction Hl.
  - reflexivity.
  - simpl.
    rewrite H.
    (* Search Permutation. *)
    apply perm_skip.
    assumption.
  - simpl.
    repeat rewrite H.
    apply perm_skip.
    apply perm_skip.
    induction l.
    + constructor.
    + simpl.
      rewrite H.
      apply perm_skip.
      assumption.
  - assumption.
Qed.

Lemma sum_prob_cover_pset_1:
  forall {A: Type} (d: Distr A),
    ProbDistr.legal d ->
    forall (l: list A),
      NoDup l ->
      incl d.(pset) l ->
      sum_prob l d.(prob) = 1%R.
Proof.
  intros.
  unfold sum_prob.
  destruct H.
  pose proof list_partition_in_notin d.(pset) l as H.
  destruct H as [t1 [t2 [? [? ?]]]].
  rewrite <- H.
  (* Search (map _ (_ ++ _)). *)
  rewrite map_app.
  rewrite sum_app.
  enough (
    sum (map d.(prob) t1) = 1%R
    /\
    sum (map d.(prob) t2) = 0%R
  ). {
    destruct H4.
    lra.
  }
  split.
  {
    enough (
      Permutation t1 d.(pset)
    ). {
      rewrite H4.
      assumption.
    }
    apply incl_nodup_perm; unfold incl.
    pose proof perm_nodup_app_l _ _ _ H H0.
    auto.
    auto.
    apply H2.
    intros.
    (* Search (In _( _++_)). *)
    destruct (in_app_or t1 t2 a) as [Hint1 | Hint2].
    - rewrite H.
      apply H1.
      auto.
    - assumption.
    - pose proof H3 _ Hint2.
      contradiction.
  }
  {
    assert (
      forall a: A, In a t2 -> (d.(prob) a <= 0)%R
    ). {
      intros.
      apply H3 in H4.
      pose proof legal_pset_valid a.
      pose proof imply_to_or _ _ H5.
      assert (~ (d.(prob) a > 0)%R) by tauto.
      lra.
    }
    assert (
      forall a: A, In a t2 -> d.(prob) a = 0%R
    ). {
      intros.
      apply Rle_antisym.
      apply H4; auto.
      apply Rge_le.
      apply legal_nonneg.
    }
    clear H H2 H3 H4.
    induction t2.
    - simpl.
      reflexivity.
    - simpl.
      simpl in H5.
      assert (forall a : A, In a t2 -> d.(prob) a = 0%R). {
        intros.
        apply H5.
        right.
        auto.
      }
      specialize (IHt2 H).
      rewrite IHt2.
      rewrite H5; try lra; auto.
  }
Qed.

Theorem ProbDistr_compute_pr_exists: forall d, exists r,
  ProbDistr.compute_pr d r.
Proof.
  intro d.
  unfold ProbDistr.compute_pr.
  induction d.(pset) as [| a pset IH].
  + exists 0%R.
    exists [].
    split; intros.
    - split; intros.
      * inversion H.
      * destruct H as [? _].
        inversion H.
    - split. reflexivity. constructor.
  + destruct IH as [r [l [? ?]]].
    destruct (classic a) as [Ha | Hna].
    {
      destruct (classic (In a l)) as [Hin | Hnin].
      - exists r.
        exists l.
        split; intros.
        --
          pose proof H P.
          destruct H1.
          split.
          ++
            intros.
            destruct H1; auto.
            split; auto.
            apply in_cons; auto.
          ++
            intros [? ?].
            destruct H3.
            subst.
            auto.
            tauto.
        --
          auto.
      - exists (r + d.(prob) a)%R.
        exists (a :: l).
        split; intros.
        --
          split; intros.
          ++
            pose proof H P.
            destruct H1.
            split.
            * left. auto.
            * subst. auto.
            * destruct H2.
              specialize (H2 H1) as [? ?].
              split; auto.
              apply in_cons; auto.
          ++
            destruct H1.
            destruct H1.
            * subst. left. auto.
            * right. apply H. tauto.
        
        --
          split.
          ++
            simpl.
            destruct H0.
            rewrite <- H0.
            rewrite Rplus_comm.
            reflexivity.
          ++
            destruct H0 as [_ H_nodup_l].
            constructor; auto.
    }
    - exists r.
      exists l.
      split; intros.
      * split; intros.
        --  pose proof H P.
            subst. split.
            ++ right. apply H2. tauto.
            ++ tauto.
        --  destruct H1.
            destruct H1.
            ++ subst. easy.
            ++ apply H. tauto.
      * destruct H0.
        rewrite H0.
        auto.
Qed. 
  
(** Level 1 *)
Definition valid_prop_sublist(l t: list Prop): Prop :=
  forall P, In P t <-> In P l /\ P.

Theorem nodup_valid_prop_sublist_perm:
  forall l t1 t2,
    NoDup t1 -> NoDup t2 ->
    valid_prop_sublist l t1 ->
    valid_prop_sublist l t2 ->
    Permutation t1 t2.
Proof.
  intros l t1 t2 H_nodup1 H_nodup2 H_valid1 H_valid2.
  unfold valid_prop_sublist in *.
  apply NoDup_Permutation; auto.
  intros P.
  specialize (H_valid1 P).
  specialize (H_valid2 P).
  tauto.
Qed.

Theorem compute_pr_same:
  forall d r1 r2,
    ProbDistr.compute_pr d r1 ->
    ProbDistr.compute_pr d r2 ->
    r1 = r2.
Proof.
  intros.
  destruct H as [l1 [? [? ?]]].
  destruct H0 as [l2 [? [? ?]]].
  enough (Permutation l1 l2). {
    subst.
    apply sum_prob_congr; auto.
    unfold eq_fun.
    reflexivity.
  }
  apply NoDup_Permutation; auto.
  intros P.
  split; intros.
  - apply H0.
    apply H.
    tauto.
  - apply H.
    apply H0.
    tauto.
Qed.

Lemma map_fst_map_pair:
  forall (T A B: Type),
  forall (lt: list T),
  forall (f: T -> (A * B)),
  map fst (map f lt) = map (fun x => fst (f x)) lt.
Proof.
  intros.
  revert lt.
  induction lt.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHlt.
    reflexivity.
Qed.

Lemma map_snd_map_pair:
  forall (T A B: Type),
  forall (lt: list T),
  forall (f: T -> (A * B)),
  map snd (map f lt) = map (fun x => snd (f x)) lt.
Proof.
  intros.
  revert lt.
  induction lt.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHlt.
    reflexivity.
Qed.

#[export] Instance ProbDistr_imply_event_refl:
  Reflexive ProbDistr.imply_event.
Proof.
  unfold Reflexive, ProbDistr.imply_event.
  intros.
  pose proof ProbDistr_compute_pr_exists x as [r ?].
  exists r, r.
  repeat split; auto.
  apply Rle_refl.
Qed.

Theorem ProbDistr_imply_event_refl_setoid:
  forall d1 d2, ProbDistr.equiv_event d1 d2 -> ProbDistr.imply_event d1 d2.
Proof. (** Level 1 *)
  intros.
  unfold ProbDistr.equiv_event, ProbDistr.imply_event in *.
  destruct H as [r1 [r2 [? [? ?]]]].
  exists r1, r2.
  repeat split; auto.
  rewrite H1.
  apply Rle_refl.
Qed.

#[export] Instance ProbDistr_equiv_equiv {A: Type}:
  Equivalence (@ProbDistr.equiv A).
Proof. (** Level 1 *)
  unfold ProbDistr.equiv.
  split.
  - unfold Reflexive.
    intros.
    split; intros.
    + reflexivity.
    + apply Permutation_refl.
  - unfold Symmetric.
    intros.
    destruct H.
    split; intros.
    + rewrite H; reflexivity.
    + rewrite H0;reflexivity.
  - unfold Transitive.
    intros.
    destruct H, H0.
    split; intros.
    + rewrite H, H0; reflexivity.
    + apply Permutation_trans with (l' := y.(pset)); tauto.
    (* + Search (Permutation _ _ -> Permutation _ _ -> Permutation _ _).  *)
Qed.



#[export] Instance ProbDistr_imply_event_trans:
  Transitive ProbDistr.imply_event.
Proof.
  unfold Transitive, ProbDistr.imply_event.
  intros x y z.
  intros [r1 [r2 [? [? ?]]]] [r2' [r3 [? [? ?]]]].
  exists r1, r3.
  repeat split; auto.
  enough (r2 = r2'). {
    subst r2'.
    (* Search (_ <= _ -> _ <= _ -> _ <= _)%R. *)
    pose proof Rle_trans _ _ _ H1 H4.
    auto.
  }
  clear H1 H4 H H3.
  unfold ProbDistr.compute_pr in *.
  destruct H0 as [l2  [? [? ?]]].
  destruct H2 as [l2' [? [? ?]]].
  apply compute_pr_same with (d := y).
  all: unfold ProbDistr.compute_pr.
  - exists l2.
    auto.
  - exists l2'.
    auto.    
Qed.

#[export] Instance ProbDistr_equiv_event_equiv:
  Equivalence ProbDistr.equiv_event.
Proof.
  unfold ProbDistr.equiv_event.
  split.
  - unfold Reflexive.
    intros.
    pose proof ProbDistr_compute_pr_exists x as [r ?].
    exists r, r.
    repeat split; auto.
  - unfold Symmetric.
    intros.
    destruct H as [r1 [r2 [? [? ?]]]].
    exists r2, r1.
    repeat split; auto.
  - unfold Transitive.
    intros.
    destruct H as [r1 [r2 [? [? ?]]]].
    destruct H0 as [r2' [r3 [? [? ?]]]].
    exists r1, r3.
    repeat split; auto.
    enough (r2 = r2'). {
      repeat subst.
      reflexivity.
    }
    clear H H3 x z r1 r3 H2 H4.
    apply compute_pr_same with (d := y); auto.
Qed.

#[export] Instance ProbDistr_imply_event_congr:
  Proper (ProbDistr.equiv_event ==>
          ProbDistr.equiv_event ==> iff) ProbDistr.imply_event.
Proof.
  unfold Proper, respectful.
  intros x y H x0 y0 H0.
  split; intros.
  - unfold ProbDistr.imply_event in *.
    destruct H1 as [r1 [r2 [? [? ?]]]].
    exists r1, r2.
    repeat split; auto.
    + unfold ProbDistr.equiv_event in H.
      destruct H as [r1' [r2' [? [? ?]]]].
      pose proof compute_pr_same _ _ _ H H1.
      subst.
      auto.
    + unfold ProbDistr.equiv_event in H0.
      destruct H0 as [r1' [r2' [? [? ?]]]].
      pose proof compute_pr_same _ _ _ H0 H2.
      subst.
      auto.
  - unfold ProbDistr.imply_event in *.
    destruct H1 as [r1 [r2 [? [? ?]]]].
    exists r1, r2.
    repeat split; auto.
    + unfold ProbDistr.equiv_event in H.
      destruct H as [r1' [r2' [? [? ?]]]].
      pose proof compute_pr_same _ _ _ H4 H1.
      subst.
      auto.
    + unfold ProbDistr.equiv_event in H0.
      destruct H0 as [r1' [r2' [? [? ?]]]].
      pose proof compute_pr_same _ _ _ H4 H2.
      subst.
      auto.
Qed.  

#[export] Instance ProbDistr_compute_pr_congr:
  Proper (ProbDistr.equiv_event ==> Sets.equiv) ProbDistr.compute_pr.
Proof.
  unfold Proper, respectful.
  intros x y H.
  destruct H as [r1 [r2 [H1 [H2 Heq]]]].
  sets_unfold.
  split.
  - intros Ha.
    pose proof compute_pr_same _ _ _ H1 Ha.
    subst.
    auto.
  - intros Ha.
    pose proof compute_pr_same _ _ _ H2 Ha.
    subst.
    auto.
Qed.

Theorem ProbDistr_compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbDistr.compute_pr f1 r1 ->
    ProbDistr.compute_pr f2 r2 ->
    ProbDistr.imply_event f1 f2 ->
    (r1 <= r2)%R.
Proof.
  intros f1 f2 r1 r2 comp1 comp2 imp.
  destruct imp as [r1' [r2' [comp1' [comp2' ?]]]].
  pose proof compute_pr_same _ _ _ comp1 comp1'.
  pose proof compute_pr_same _ _ _ comp2 comp2'.
  subst.
  auto.
Qed.

(*********************************************************)
(**                                                      *)
(** Probability Monad                                    *)
(**                                                      *)
(*********************************************************)

Module ProbMonad.

Record Legal {A: Type} (f: Distr A -> Prop): Prop := {
  Legal_exists: exists d, d ∈ f;
  Legal_legal: forall d, d ∈ f -> ProbDistr.legal d;
  Legal_unique: forall d1 d2, d1 ∈ f -> d2 ∈ f -> ProbDistr.equiv d1 d2;
  Legal_congr: forall d1 d2, ProbDistr.equiv d1 d2 -> d1 ∈ f -> d2 ∈ f;
}.

Record M (A: Type): Type :=
{
  distr: Distr A -> Prop;
  legal: Legal distr;
}.

Arguments distr {_} _.
Arguments legal {_} _.

Definition __ret {A: Type} (a: A) : Distr A -> Prop :=
  ProbDistr.is_det a.

Lemma __ret_Legal {A: Type}: 
  forall a: A, Legal (__ret a).
Proof.
  intros.
  constructor.
  - exists {| ProbDistr.prob := (fun a' => if eq_dec a a' then 1%R else 0%R);
              ProbDistr.pset := [a] |}.
    sets_unfold.
    unfold __ret.
    unfold ProbDistr.is_det.
    repeat split; simpl.
    +
      destruct (eq_dec a a).
      * reflexivity.
      * tauto.
    + intros.
      destruct (eq_dec a b).
      * subst.
        contradiction.
      * reflexivity.

  - sets_unfold.
    intros.
    unfold __ret in *.
    unfold ProbDistr.is_det in *.
    destruct H as [? [? ?]].
    split.
    + rewrite H.
      constructor; simpl; auto.
      apply NoDup_nil.
    + intros.
      destruct (eq_dec a a0).
      * subst.
        rewrite H0.
        (* Search (_ <= _ -> _ >= _)%R. *)
        apply Rle_ge.
        apply Rle_0_1.
      * specialize (H1 a0 n).
        rewrite H1.
        apply Rle_refl.
    + intros.
      destruct (eq_dec a a0).
      * subst.
        rewrite H.
        simpl; auto.
      * specialize (H1 a0 n).
        rewrite H1 in H2.
        pose proof Rgt_irrefl 0%R.
        contradiction.
    + rewrite H.
      unfold sum_prob.
      simpl.
      rewrite H0.
      apply Rplus_0_r.
  - sets_unfold.
    intros.
    unfold __ret in *.
    unfold ProbDistr.is_det in *.
    destruct H as [? [? ?]].
    destruct H0 as [? [? ?]].
    unfold ProbDistr.equiv.
    split; intros.
    + destruct (eq_dec a a0).
      * subst.
        rewrite H3, H1.
        reflexivity.
      * specialize (H2 a0 n).
        specialize (H4 a0 n).
        rewrite H2.
        rewrite H4.
        reflexivity.
    + rewrite H, H0.
      reflexivity.
  - sets_unfold.
    intros.
    unfold __ret in *.
    unfold ProbDistr.is_det in *.
    unfold ProbDistr.equiv in *.
    destruct H as [H_prob_eq H_pset_perm].
    destruct H0 as [H_d1_pset [H_d1_prob H_d1_prob_0]].
    assert (
      d1.(prob)=d2.(prob)
    ) as H_prob_func_eq
    by (apply functional_extensionality; assumption).
    repeat split.
    + rewrite H_d1_pset in H_pset_perm.
      (* Search (Permutation _ _ -> _ = _). *)
      apply Permutation_length_1_inv.
      assumption.
    + rewrite <- H_prob_func_eq.
      assumption.
    + rewrite <- H_prob_func_eq.
      assumption.
Qed.
        

Definition ret {A: Type} (a: A) : M A :=
  {|
    distr := __ret a;
    legal := __ret_Legal a;
  |}.

(* 
  概率单子的bind操作如下定义：
  给定一个概率单子 f: Distr A -> Prop （即 f 是一个 Distr A 的集合），
  一个函数 g: A -> Distr B -> Prop （即 g 是一个从 A 到 Distr B 的集合的函数），
  得到的是一个 Distr B -> Prop，即一个 Distr B 的集合。
  每个 s2 ∈ __bind f g 都满足以下条件：
  存在一个 s1 ∈ f；
  对于 s1 的每个元素 a，其概率是 prob a，被 g a 映射到的集合内存在一个分布 d；
  s2 上的概率是 prob a 乘以 d.(prob) a 对于 s1 的每个元素 a 求和。
*)
Definition __bind {A B: Type}
                  (f: Distr A -> Prop)
                  (g: A -> Distr B -> Prop)
                  (s2: Distr B): Prop :=
  exists (s1: Distr A) l,
    s1 ∈ f /\
    Forall2
      (fun a '(r, d) =>
         r = s1.(prob) a /\ d ∈ g a)
      s1.(pset) l /\
    ProbDistr.sum_distr l s2.


Lemma __bind_legal {A B: Type}:
  forall (f: Distr A -> Prop) (g: A -> Distr B -> Prop),
    Legal f ->
    (forall a, Legal (g a)) ->
    Legal (__bind f g).
Proof.
  intros f g H_legal_f H_all_legal_g.
  split.
  {
    sets_unfold.
    unfold __bind.
    destruct H_legal_f as [[da Hda] H_legal_f H_unique_f].
    specialize (H_legal_f da Hda).
    destruct H_legal_f as [Hda_nodup Hda_nonneg Hda_pset_valid Hda_prob_1].
    clear Hda_prob_1.
    clear Hda_pset_valid.

    enough (
      exists  (s1 : Distr A) (d : Distr B) (l : list (R * Distr B)),
        s1 ∈ f /\
        Forall2 (fun (a : A) '(r, d0) => r = s1.(prob) a /\ d0 ∈ g a)
          s1.(pset) l /\ ProbDistr.sum_distr l d
    ) by firstorder.
    exists da.
    induction da.(pset) as [| a pset IH].
    2: {
      (* Search (NoDup (_ :: _)). *)
      pose proof NoDup_cons_iff a pset as [H_nodup _].
      specialize (H_nodup Hda_nodup).
      destruct H_nodup as [_ H_nodup].
      specialize (IH H_nodup).
      clear H_nodup.
      destruct IH as [d_induction [l_induction [IH1 [IH2 IH3]]]].
      enough (
        exists (l : list (R * Distr B)),
          da ∈ f /\
          Forall2 (fun (a0 : A) '(r, d0) => r = da.(prob) a0 /\ d0 ∈ g a0)
            (a :: pset) l /\ 
            (exists (d : Distr B), ProbDistr.sum_distr l d)
      ) by firstorder.
      pose proof H_all_legal_g a as H_legal_g_a.
      destruct H_legal_g_a as [H_exists_g_a H_legal_g_a H_unique_g_a].
      destruct H_exists_g_a as [ga Hd0].

      exists ((da.(prob) a, ga) :: l_induction).
      split; auto.
      split.
      - constructor; auto.
      - exists {| 
                  ProbDistr.pset := filter_dup (ga.(pset) ++ d_induction.(pset));
                  ProbDistr.prob := (fun b: B => (da.(prob) a * ga.(prob) b +
                  sum (map (fun '(r, d) => r * d.(prob) b) l_induction))%R )
               |}.
        split; simpl.
        +
          apply perm_filter_dup_cons.
          destruct IH3.
          assert (NoDup d_induction.(pset)) as H_nodup_d_induction. {
            apply perm_filter_dup_nodup with (l2 := (concat (map (fun '(_, d) => d.(pset)) l_induction))).
            assumption.
          }
          pose proof nodup_perm_filter_dup _ H_nodup_d_induction as H_perm_d_induction.
          apply Permutation_trans with (l' := d_induction.(pset)).
          * apply Permutation_sym; assumption.
          * assumption.
        +
          intros b.
          reflexivity.
    }
    enough(
      exists (l : list (R * Distr B)),
        da ∈ f /\
        Forall2 (fun (a : A) '(r, d0) => r = da.(prob) a /\ d0 ∈ g a) [] l /\
        (exists (d : Distr B), ProbDistr.sum_distr l d)
    ) by firstorder.
    exists [].
    split; auto.
    split.
    * constructor.
    * exists {| ProbDistr.pset := [];
               ProbDistr.prob := (fun b: B => 0%R) |}.
      split; simpl; intros; auto; split; auto.
  } (* Existence finished *)
  {
    sets_unfold.
    intros d H_d_is_bind_f_g.
    unfold __bind in H_d_is_bind_f_g.
    destruct H_d_is_bind_f_g as [da [l [H_da_in_f [H_forall2 H_sum_distr]]]].
    destruct H_sum_distr as [H_sum_pset_valid H_sum_prob_valid].
    split.
    - pose proof perm_filter_dup_nodup _ _ H_sum_pset_valid.
      assumption.
    - intros b.
      specialize (H_sum_prob_valid b).
      rewrite H_sum_prob_valid.
      enough (
        forall '(r, d), In (r, d) l ->
          (r * d.(prob) b >= 0)%R
      ). {
        clear H_forall2.
        clear H_sum_pset_valid.
        clear H_sum_prob_valid.
        induction l as [| [ri di] l IH].
        - unfold sum, map.
          simpl.
          apply Rle_refl.
        - simpl in H.
          assert (
            (forall '(r, d), (ri, di) = (r, d)  -> (r * d.(prob) b >= 0)%R)
            /\
            (forall '(r, d), In (r, d) l -> (r * d.(prob) b >= 0)%R)

          ). {
            split.
            - intros [r1 d1].
              specialize (H (r1, d1)).
              intros.
              apply H.
              auto.
            - intros [r1 d1] H_in_l.
              specialize (H (r1, d1)).
              intros.
              apply H.
              right.
              auto. 
          }
          destruct H0 as [H0_1 H0_2].
          specialize (IH H0_2).
          unfold sum.
          simpl.
          enough (
            (ri * di.(prob) b >= 0)%R
            /\
            (fold_right Rplus 0 (map (fun '(r, d0) => r * d0.(prob) b) l) >= 0)%R
          ) as H1. {
            destruct H1.
            (* Search (_ >= _ -> _ >= _ -> _ >= _)%R. *)
            pose proof Rplus_ge_compat _ _ _ _ H0 H1.
            (* Search (0 + _)%R. *)
            rewrite Rplus_0_l in H2.
            auto.
          }
          split.
          + specialize (H0_1 (ri, di)).
            apply H0_1.
            auto.
          + exact IH.
      }
      intros [r db] H_in_l.
      clear H_sum_pset_valid H_sum_prob_valid.
      (* Search (Forall2). *)
      induction H_forall2.
      * inversion H_in_l.
      * destruct H_in_l.
        {
          subst.
          destruct H as [H_prob_eq H_db_in_g].
          destruct H_legal_f as [_ H_legal_f _].
          pose proof (H_legal_f da H_da_in_f) as legal_da.
          destruct legal_da as [_ H_nonneg_da _ _].
          pose proof H_nonneg_da x as r_nonneg.
          rewrite <- H_prob_eq in r_nonneg.
          clear H_nonneg_da H_prob_eq.
          specialize (H_all_legal_g x).
          destruct H_all_legal_g as [_ H_legal_g_x _].
          pose proof H_legal_g_x db H_db_in_g as legal_db.
          destruct legal_db as [_ H_nonneg_db _ _].
          pose proof H_nonneg_db b as nonneg_db.
          (* Search (_ * _ >= _)%R. *)
          assert (forall x y, (x >= 0)%R -> (y >= 0)%R -> (x * y >= 0)%R) as Rmult_ge_0. {
            intros.
            pose proof Rmult_ge_compat_l x0 y 0 H H0.
            rewrite Rmult_0_r in H1.
            auto.
          }
          apply Rmult_ge_0; auto.
        }
        {
          apply IHH_forall2.
          auto.
        }
    - intros b.
      specialize (H_sum_prob_valid b).
      rewrite H_sum_prob_valid.
      intros H.
      assert (
        exists '(r, d), In (r, d) l /\ (r * d.(prob) b > 0)%R
      ). {
        clear H_sum_prob_valid.
        clear H_sum_pset_valid.
        clear H_forall2.
        induction l as [| [ri di] l IH].
        - simpl in H.
          pose proof Rgt_irrefl 0%R.
          contradiction.
        - simpl in H.
          (* H: (_ + _)>0. so either of them should be > 0. *)
          destruct (Rgt_dec (ri * di.(prob) b) 0%R) as [H_pos | H_nonpos].
          + exists (ri, di).
            simpl; auto.
          + 
            (* Search (~ (_ > _)%R -> _ <= _)%R. *)
            pose proof Rnot_gt_le _ _ H_nonpos.
            (* Search (_ >= _)%R. *)
            rewrite Rplus_comm in H.
            pose proof Rle_ge _ _ H0.
            pose proof Rplus_gt_reg_neg_r _ _ _ H1 H.
            specialize (IH H2).
            destruct IH as [[rii dii] [H_in_l H_pos]].
            exists (rii, dii).
            simpl; auto.
      }
      destruct H0 as [[ri di] [H_in_l H_pos]].
      (* Search (Permutation _ _ -> In _ _ -> In _ _). *)
      apply Permutation_in with (l := (filter_dup (concat (map (fun '(_, d) => d.(pset)) l)))).
      + 
        apply Permutation_sym.
        assumption.
      +
        apply filter_dup_in_inv.
        apply in_concat.
        exists (di.(pset)).
        split.
        * clear H_sum_prob_valid H_sum_pset_valid H_forall2 H.
          induction l as [| [rii dii] l IH].
          -- simpl in H_in_l.
             contradiction.
          -- simpl in H_in_l.
             destruct H_in_l.
             ++ inversion H.
                subst.
                simpl.
                left.
                auto.
              ++ right.
                apply IH.
                auto.
        * 
          (* prove that ri>0 and di is legal *)
          (* Search Forall2. *)
          pose proof Forall2_in_r_exists _ _ _ H_forall2 _ H_in_l as [a [H_a_in_apset [H_prob_eq H_ga_in_g]]].
          pose proof H_all_legal_g a as [_ H_all_ga_legal _].
          pose proof H_all_ga_legal _ H_ga_in_g as [_ H_ga_nonneg H_ga_pset_valid _].
          apply H_ga_pset_valid.
          destruct (eq_dec (di.(prob) b) 0%R) as [H_eq | H_neq].
          --
            subst.
            rewrite H_eq in H_pos.
            (* Search (_ * 0)%R. *)
            rewrite Rmult_0_r in H_pos.
            pose proof Rgt_irrefl 0%R.
            contradiction.
          --
            specialize (H_ga_nonneg b).
            apply Rge_ne_gt; auto.
    -
      pose proof sum_prob_congr _ _ H_sum_pset_valid _ _ H_sum_prob_valid as H_sum_prob_valid_2.
      rewrite H_sum_prob_valid_2.
      clear H_sum_prob_valid_2.
      clear H_sum_pset_valid.
      clear H_sum_prob_valid.
      unfold sum_prob.
      pose proof sum_map_sum_map _ _ (filter_dup (concat (map (fun '(_, d0) => d0.(pset)) l))) l.
      specialize (H
        (
          fun '(r, d0) => 
            fun b: B => 
              (r * d0.(prob) b)%R
        )
      ).
      simpl in H.
      assert (
        sum
          (map
            (fun a : B =>
              sum
                (map
                  (fun b : R * Distr B =>
                    (let '(r, d0) := b in fun b0 : B => (r * d0.(prob) b0)%R) a) l))
            (filter_dup (concat (map (fun '(_, d0) => d0.(pset)) l))))
      =
      sum
        (map (fun a : B => sum (map (fun '(r, d0) => (r * d0.(prob) a)%R) l))
          (filter_dup (concat (map (fun '(_, d0) => d0.(pset)) l))))
      ) as H_eq. {
        f_equal.
        f_equal.
        extensionality a.
        f_equal.
        f_equal.
        extensionality b.
        destruct b as [r d0].
        reflexivity.
      }
      rewrite <- H_eq.
      clear H_eq.
      rewrite H.
      clear H.
      enough (
        (map
          (fun b : R * Distr B =>
            sum
              (map
                (fun a : B => (let '(r, d0) := b in fun b0 : B => (r * d0.(prob) b0)%R) a)
                (filter_dup (concat (map (fun '(_, d0) => d0.(pset)) l))))) l)
        =
        map fst l
      ). {
        rewrite H.
        clear H.
        enough (
          map fst l
          =
          map da.(prob) da.(pset)
        ). {
          rewrite H.
          clear H.
          destruct H_legal_f as [_ H_f_legal _].
          specialize (H_f_legal da H_da_in_f).
          destruct H_f_legal as [_ _ _ prob1].
          apply prob1.
        }
        induction H_forall2.
        - simpl.
          reflexivity.
        - simpl.
          rewrite IHH_forall2.
          destruct y.
          destruct H.
          simpl.
          subst.
          reflexivity.
      }
      (* Search map. *)
      apply map_ext_in.
      intros [r d0] H_in_l.
      simpl.
      (* Search Forall2. *)
      pose proof Forall2_in_r_exists _ _ _ H_forall2 _ H_in_l as [a [H_a_in_apset [H_prob_eq H_ga_in_g]]].
      pose proof H_all_legal_g a as [_ H_all_ga_legal _].
      pose proof H_all_ga_legal _ H_ga_in_g as [H_ga_pset_valid H_ga_nonneg H_ga_legal H_ga_prob_1].
      pose proof sum_map_multi (filter_dup (concat (map (fun '(_, d1) => d1.(pset)) l))) d0.(prob) r.
      rewrite H.
      clear H.
      enough (
        sum (map d0.(prob) (filter_dup (concat (map (fun '(_, d1) => d1.(pset)) l))))%R = 1%R
      ). {
        rewrite H.
        lra.
      }
      apply sum_prob_cover_pset_1; auto.
      * apply filter_dup_nodup.
      * apply filter_dup_incl_list.
        assert (
          In d0.(pset)
          (map (fun '(_, d1) => d1.(pset)) l)
        ). {
          pose proof in_map (fun '(_, d1) => d1.(pset)) l (r, d0) H_in_l.
          simpl in H.
          auto.
        }
        apply in_listlist_concat_incl.
        auto.
  }  (* Legal finished *)
  {
    sets_unfold.
    intros d1 d2 H_d1_is_bind_f_g H_d2_is_bind_f_g.
    unfold __bind in *.
    destruct H_d1_is_bind_f_g as [da1 [l1 [H_da1_in_f [H_forall2_1 H_sum_distr_1]]]].
    destruct H_d2_is_bind_f_g as [da2 [l2 [H_da2_in_f [H_forall2_2 H_sum_distr_2]]]].
    split.
    {
      intros b.
      destruct H_sum_distr_1 as [_ H_sum_prob_valid_1].
      destruct H_sum_distr_2 as [_ H_sum_prob_valid_2].
      rewrite H_sum_prob_valid_1, H_sum_prob_valid_2.
      clear H_sum_prob_valid_1 H_sum_prob_valid_2.
      pose proof (Legal_unique f) H_legal_f _ _ H_da1_in_f H_da2_in_f as H_equiv_da1_da2.
      destruct H_equiv_da1_da2 as [H_prob_equiv_da12 H_pset_perm_da12].
      enough 
      (Permutation (map (fun '(r, d) => (r * d.(prob) b)%R) l1) 
                   (map (fun '(r, d) => (r * d.(prob) b)%R) l2)). {
        apply sum_congr.
        assumption.
      }
      (* Search Forall2. *)
      (* enough (
        exists l3,
          Permutation (map (fun '(r, d) => (r * d.(prob) b)%R) l1) l3 /\
          Permutation (map (fun '(r, d) => (r * d.(prob) b)%R) l2) l3
      ). {
        destruct H as [l3 [H_perm_1 H_perm_2]].
        rewrite H_perm_1.
        rewrite H_perm_2.
        reflexivity.
      } *)

      assert (
        forall l1 l2,
          forall perm1 perm2,
            Permutation da1.(pset) perm1 ->
            Permutation da1.(pset) perm2 ->
            Forall2 (fun (a : A) '(r, d) => r = da1.(prob) a /\ d ∈ g a) perm1 l1 ->
            Forall2 (fun (a : A) '(r, d) => r = da1.(prob) a /\ d ∈ g a)
            perm2 l2 ->
            perm_after_map (fun '(r, d) => (r * d.(prob) b)%R) l1 l2
      ). {
        clear l1 l2 H_forall2_1 H_forall2_2.
        clear d1 d2 da2 H_prob_equiv_da12 H_pset_perm_da12 H_da2_in_f.
        intros.
        sets_unfold in H1.
        sets_unfold in H2.
        (* Search Forall2. *)

        symmetry in H.
        pose proof Permutation_trans as H_perm.
        specialize (H_perm _ _ _ _ H H0).
        pose proof Permutation_Forall2 as H_perm_forall2.
        specialize (H_perm_forall2 _ _ _ _ _ _ H_perm H1).
        destruct H_perm_forall2 as [l1' [H_perm_l1_l1' H1']].
        clear H1.
        rewrite H_perm_l1_l1'.
        clear H_perm_l1_l1' l1.
        remember l1' as l1; subst l1'.
        clear perm1 H H_perm.
        remember perm2 as perm; subst perm2.
        symmetry in H0.
        pose proof Permutation_Forall2 H0 H2 as [l2'' [H_perm_l2_l2'' H2']]. 
        pose proof Permutation_Forall2 H0 H1' as [l1'' [H_perm_l1_l1'' H1'']].
        rewrite H_perm_l2_l2'', H_perm_l1_l1''.
        clear l1 l2 H_perm_l2_l2'' H_perm_l1_l1'' H2 H1'.
        clear H0 perm.
        remember H1'' as H1; clear H1'' HeqH1.
        remember H2' as H2; clear H2' HeqH2.
        remember l1'' as l1; subst l1''.
        remember l2'' as l2; subst l2''.

        unfold perm_after_map.
        (* now the order are aligned *)
        enough (
          (map (fun '(r, d) => (r * d.(prob) b)%R) l1)
          =
          (map (fun '(r, d) => (r * d.(prob) b)%R) l2)
        ). {
          rewrite H.
          reflexivity.
        }
        (* Search map. *)
        remember (fun (a : A) '(r, d) => r = da1.(prob) a /\ g a d) as pred.
        remember (fun '(r, d) => (r * d.(prob) b)%R) as cal.
        assert (
          forall a t1 t2,
          In a da1.(pset) ->
          In t1 l1 ->
          In t2 l2 ->
          pred a t1 ->
          pred a t2 ->
          cal t1 = cal t2
        ). {
          intros.
          subst pred.
          subst cal.
          destruct t1 as [r1 d1], t2 as [r2 d2].
          destruct H5.
          destruct H4.
          enough (
           (r1=r2)%R /\ (d1.(prob) b = d2.(prob) b)%R
          ) as HH. {
            destruct HH as [HH1 HH2].
            rewrite HH1, HH2.
            reflexivity.
          }
          split.
          - lra.
          - pose proof H_all_legal_g a as [_ _ H_all_ga_unique].
            specialize (H_all_ga_unique _ _ H7 H6).
            destruct H_all_ga_unique as [H_prob_eq H_ga_unique].
            apply H_prob_eq.
        }
        enough (
          Forall2 (fun x1 x2 => cal x1 = cal x2) l1 l2
        ) as H_forall2. {
          clear H1 H2 H.
          induction H_forall2.
          - constructor.
          - simpl.
            rewrite H, IHH_forall2.
            reflexivity.
        }
        pose proof Forall2_pair_Forall2 pred (fun x1 x2 : R * Distr B => cal x1 = cal x2) da1.(pset) l1 l2.
        eapply H0.
        all: auto.
      }
      assert (da1.(prob) = da2.(prob)) as H_prob_eq. {
        exact (functional_extensionality da1.(prob) da2.(prob) H_prob_equiv_da12).
      }
      assert (Permutation da1.(pset) da1.(pset)) as H_perm by auto.
      rewrite <- H_prob_eq in H_forall2_2.
      specialize (H _ _ _ _ H_perm H_pset_perm_da12 H_forall2_1 H_forall2_2).
      exact H.
    }
    {
      destruct H_sum_distr_1 as [H_sum_pset_valid_1 _].
      destruct H_sum_distr_2 as [H_sum_pset_valid_2 _].
      rewrite H_sum_pset_valid_1, H_sum_pset_valid_2.
      clear H_sum_pset_valid_1 H_sum_pset_valid_2.
      (* Search filter_dup. *)
      apply perm_filter_dup_incl.
      intros b.
      split.
      {
        intros H.
        pose proof in_concat (map (fun '(_, d) => d.(pset)) l1) b as [H_inb _]; specialize (H_inb H).
        destruct H_inb as [lb [H_lb H_inb]].
        (* Search map. *)
        pose proof in_map_iff (fun '(_, d) => d.(pset)) l1 lb as [H_lb_in_l1 _]; specialize (H_lb_in_l1 H_lb).
        destruct H_lb_in_l1 as [db [H_db_eq H_db_in_l1]].
        pose proof Forall2_in_r_exists _ _ _ H_forall2_1 _ H_db_in_l1.
        destruct H0 as [a [? ?]].

        assert (Permutation da1.(pset) da2.(pset)) as H_perm. {
          destruct H_legal_f as [_ _ H_unique_f].
          specialize (H_unique_f da1 da2 H_da1_in_f H_da2_in_f).
          destruct H_unique_f as [? ?].
          auto.
        }
        assert (In a da2.(pset)) as H_in_a2. {
          apply Permutation_in with (l := da1.(pset)); auto.
        }
        pose proof Forall2_in_l_exists _ _ _ H_forall2_2 _ H_in_a2 as [b2 [? ?]].
        destruct db.
        destruct b2.
        subst.
        apply in_concat.
        exists (d0.(pset)).
        split; auto.
        {
          apply in_map_iff.
          exists (r0, d0).
          split; auto.
        }
        {
          destruct H1, H3.
          (* d and d0 all ∈ g a *)
          pose proof H_all_legal_g a as [_ _ H_all_ga_legal].
          specialize (H_all_ga_legal _ _ H4 H5).
          destruct H_all_ga_legal as [_ Hperm].
          pose proof Permutation_in _ Hperm H_inb.
          auto.
        }
      }
      {
        intros H.
        pose proof in_concat (map (fun '(_, d) => d.(pset)) l2) b as [H_inb _]; specialize (H_inb H).
        destruct H_inb as [lb [H_lb H_inb]].
        pose proof in_map_iff (fun '(_, d) => d.(pset)) l2 lb as [H_lb_in_l2 _]; specialize (H_lb_in_l2 H_lb).
        destruct H_lb_in_l2 as [db [H_db_eq H_db_in_l2]].
        pose proof Forall2_in_r_exists _ _ _ H_forall2_2 _ H_db_in_l2.
        destruct H0 as [a [? ?]].

        assert (Permutation da1.(pset) da2.(pset)) as H_perm. {
          destruct H_legal_f as [_ _ H_unique_f].
          specialize (H_unique_f da1 da2 H_da1_in_f H_da2_in_f).
          destruct H_unique_f as [? ?].
          auto.
        }
        assert (In a da1.(pset)) as H_in_a1. {
          apply Permutation_in with (l := da2.(pset)); auto.
          symmetry; auto.
        }
        pose proof Forall2_in_l_exists _ _ _ H_forall2_1 _ H_in_a1 as [b1 [? ?]].
        destruct db.
        destruct b1.
        subst.
        apply in_concat.
        exists (d0.(pset)).
        split; auto.
        {
          apply in_map_iff.
          exists (r0, d0).
          split; auto.
        }
        {
          destruct H1, H3.
          (* d and d0 all ∈ g a *)
          pose proof H_all_legal_g a as [_ _ H_all_ga_legal].
          specialize (H_all_ga_legal _ _ H4 H5).
          destruct H_all_ga_legal as [_ Hperm].
          pose proof Permutation_in _ Hperm H_inb.
          auto.
        }
      }
    }
  }
  {
    sets_unfold.
    intros d1 d2 H_equiv_d1_d2.
    destruct H_equiv_d1_d2 as [H_prob_equiv_d1_d2 H_pset_perm_d1_d2].
    unfold __bind.
    intros H_bind_f_g_d1.
    destruct H_bind_f_g_d1 as [da1 [l1 [H_da1_in_f [H_forall2_1 H_sum_distr_1]]]].
    exists da1, l1.
    split; auto.
    split; auto.
    destruct H_sum_distr_1 as [H_sum_pset_valid_1 H_sum_prob_valid_1].
    split.
    - transitivity d1.(pset); auto.
      symmetry; auto.
    - intros b.
      pose proof H_prob_equiv_d1_d2 b.
      rewrite <- H.
      apply H_sum_prob_valid_1.
  }
Qed.


Definition bind {A B: Type} (f: M A) (g: A -> M B): M B :=
  {|
    distr := __bind f.(distr) (fun a => (g a).(distr));
    legal := __bind_legal _ _ f.(legal) (fun a => (g a).(legal));
  |}.

Definition compute_pr (f: M Prop): SetMonad.M R :=
  fun r => exists (d: Distr Prop), d ∈ f.(distr) /\ ProbDistr.compute_pr d r.

Definition imply_event (f1 f2: M Prop): Prop :=
  exists d1 d2,
    d1 ∈ f1.(distr) /\ d2 ∈ f2.(distr) /\ ProbDistr.imply_event d1 d2.

Definition equiv {A: Type} (f1 f2: M A): Prop :=
  f1.(distr) == f2.(distr).

Definition equiv_event (f1 f2: M Prop): Prop :=
  exists d1 d2,
    d1 ∈ f1.(distr) /\ d2 ∈ f2.(distr) /\ ProbDistr.equiv_event d1 d2.

End ProbMonad.

#[export] Instance ProbMonad: Monad ProbMonad.M := {|
  bind := @ProbMonad.bind;
  ret := @ProbMonad.ret;
|}.

Notation "x == y" := (ProbMonad.equiv x y): monad_scope.
Notation "x === y" := (ProbMonad.equiv_event x y) (at level 61): monad_scope.
Notation "x '.(distr)'" := (ProbMonad.distr x) (at level 1).
Notation "x '.(legal)'" := (ProbMonad.legal x) (at level 1).
Notation "x '.(Legal_exists)'" := (ProbMonad.Legal_exists _ x) (at level 1).
Notation "x '.(Legal_legal)'" := (ProbMonad.Legal_legal _ x) (at level 1).
Notation "x '.(Legal_unique)'" := (ProbMonad.Legal_unique _ x) (at level 1).
Notation "x '.(Legal_congr)'" := (ProbMonad.Legal_congr _ x) (at level 1).

Definition Always {A: Type} (c: ProbMonad.M A) (P: A -> Prop): Prop :=
  Hoare (ProbMonad.compute_pr (res <- c;; ret (P res))) (fun pr => pr = 1%R).

Lemma Forall2_to_forall:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f l1 l2 ->
    Forall (fun '(a, b) => f a b) (combine l1 l2).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl.
    constructor; auto.
Qed.

Lemma perm_filter_dup_notin:
  forall {A: Type} (l: list A) (a: A),
    ~ In a (filter_dup l) ->
    Permutation (filter_dup (a :: l)) (a :: filter_dup l).
Admitted.

Lemma perm_filter_dup_in:
  forall {A: Type} (l: list A) (a: A),
    In a (filter_dup l) ->
    Permutation (filter_dup (a :: l)) (filter_dup l).
Admitted.

Lemma in_exists_remaining_list_perm:
  forall {A: Type} (l: list A) (a: A) ,
    In a l -> exists l', Permutation l (a :: l').
Proof.
  induction l.
  - contradiction.
  - intros.
    destruct H.
    + subst.
      exists l.
      apply Permutation_refl.
    + specialize (IHl a0 H).
      destruct IHl as [l' H_perm].
      exists (a :: l').
      (* Search Permutation. *)
      pose proof perm_swap a a0 l' as H_swap.
      pose proof Permutation_trans.
      specialize (H0 A (a :: l) (a :: a0 :: l') (a0 :: a :: l')).
      apply H0.
      * apply Permutation_cons; auto.
      * apply Permutation_sym.
        apply H_swap.
Qed.

Lemma in_map_eq:
  forall {A B: Type} (f: A -> B) (g: A -> B) (l: list A),
    (forall a, In a l -> f a = g a) -> 
    map f l = map g l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    f_equal.
    + apply H.
      simpl; auto.
    + apply IHl.
      intros.
      apply H.
      simpl; auto.
Qed.

Lemma not_in_filter_dup_remove:
  forall {A: Type} (l1 l2: list A) (a: A),
    ~ In a (filter_dup (l1 ++ l2)) -> ~ In a (filter_dup l2).
Proof.
Admitted.

Lemma prob_zero_1:
  forall {A: Type} (l: list (R * Distr Prop)) (d0: Distr Prop) (la: list A) (dA: Distr A) (Q: A -> Prop) (a: A),
    ProbDistr.sum_distr l d0 ->
    Forall2
      (fun (a : A) '(r, d) =>
        r = dA.(prob) a /\
        d.(pset) = [Q a] /\
        d.(prob) (Q a) = 1%R /\
        (forall b : Prop, Q a <> b -> d.(prob) b = 0%R)) la l ->
    ~ In (Q a) d0.(pset) ->
    forall rd, In rd l -> (fst rd * (snd rd).(prob) (Q a) = 0)%R.
    (* sum (map (fun '(r0, d0) => (r0 * d0.(prob) (Q a))%R) l) = 0%R. *)
Proof.
  induction l as [| [r d] l IH].
  + intros.
    contradiction.
  + intros.
    destruct la as [| a0 la'].
    - inversion H0.
    - assert (exists d0', ProbDistr.sum_distr l d0') as [d0' ?]. {
        set (d0'_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) l))).
        set (d0'_prob := fun Pa => sum (map (fun '(r0, d) => (r0 * d.(prob) Pa)%R) l)).
        set (d0' := {| ProbDistr.pset := d0'_pset; ProbDistr.prob := d0'_prob; |}).
        exists d0'.
        split; auto.
      }
      inversion H0.
      subst.
      specialize (IH d0' la' dA Q a H3 H9).
      assert (~ In (Q a) d0'.(pset)). {
        destruct H as [H _].
        simpl in H.
        destruct H3 as [H3 _].
        assert (~ In (Q a) (filter_dup (d.(pset) ++ concat (map (fun '(_, d) => d.(pset)) l)))). {
          unfold not.
          intros.
          pose proof Permutation_in as H_perm_in.
          apply Permutation_sym in H.
          specialize (H_perm_in Prop (filter_dup (d.(pset) ++ concat (map (fun '(_, d) => d.(pset)) l))) d0.(pset) (Q a) H H4).
          contradiction.
        }
        pose proof not_in_filter_dup_remove (d.(pset)) (concat (map (fun '(_, d) => d.(pset)) l)) (Q a) H4 as H_not_in.
        unfold not.
        intros.
        unfold not in H_not_in.
        apply H_not_in.
        pose proof Permutation_in as H_perm_in.
        specialize (H_perm_in Prop d0'.(pset) (filter_dup (concat (map (fun '(_, d1) => d1.(pset)) l))) (Q a) H3 H5).
        assumption.
      }
      specialize (IH H4 rd).
      destruct H2.
      * subst.
        simpl.
        assert ((forall b : Prop, Q a0 <> b -> d.(prob) b = 0%R)) by apply H7.
        specialize (H2 (Q a)).
        assert (Q a0 <> Q a). {
          destruct H as [H _].
          simpl in H.
          assert (d.(pset) = [Q a0]) by apply H7.
          rewrite H5 in H.
          assert (In (Q a0) d0.(pset)). {
            assert (In (Q a0) ([Q a0] ++ concat (map (fun '(_, d) => d.(pset)) l))). {
              simpl.
              left; auto.
            }
            pose proof filter_dup_in_iff ([Q a0] ++ concat (map (fun '(_, d) => d.(pset)) l)) (Q a0) as [? _].
            specialize (H8 H6).
            pose proof Permutation_in.
            apply Permutation_sym in H.
            specialize (H10 Prop (filter_dup ([Q a0] ++ concat (map (fun '(_, d) => d.(pset)) l))) d0.(pset) (Q a0) H H8).
            assumption.
          }
          destruct (eq_dec (Q a0) (Q a)) as [H_eq | H_neq].
          -- rewrite H_eq in H6.
            contradiction.
          -- assumption.
        }
        specialize (H2 H5).
        rewrite H2.
        lra. 
      * specialize (IH H2).
        simpl.
        auto.
Qed.

Lemma prob_zero_2:
  forall {A: Type} (d0: Distr Prop) (la: list A) (dA: Distr A) (Q: A -> Prop) (a: A) (l: list (R * Distr Prop)),
    (forall rd, In rd l -> (fst rd * (snd rd).(prob) (Q a) = 0)%R) ->
    sum (map (fun '(r0, d0) => (r0 * d0.(prob) (Q a))%R) l) = 0%R.
Proof.
  induction l as [| [r d] l IH].
  - intros.
    simpl.
    lra.
  - intros.
    simpl.
    assert (r * d.(prob) (Q a) = 0)%R. {
      apply (H (r, d)).
      left; auto.
    }
    rewrite H0.
    assert (forall rd : R * Distr Prop, In rd l -> (fst rd * (snd rd).(prob) (Q a))%R = 0%R). {
      intros.
      apply H.
      right; auto.
    }
    specialize (IH H1).
    rewrite IH.
    lra.
Qed.  

Lemma sum_prob1:
  forall {A : Type} (dA : Distr A) (dQ : Distr Prop) (Q : A -> Prop) (lQ : list (R * Distr Prop)) (sum_r : R),
    Forall2
      (fun (a : A) '(r, d) =>
        r = dA.(prob) a /\ d.(pset) = [Q a] /\ d.(prob) (Q a) = 1%R /\ 
        (forall b : Prop, Q a <> b -> d.(prob) b = 0%R))
      dA.(pset) lQ ->
    ProbDistr.sum_distr lQ dQ ->
    sum (map dA.(prob) dA.(pset)) = sum_r ->
    sum (map dQ.(prob) dQ.(pset)) = sum_r.
Proof.
  intros A dA.
  induction dA.(pset) as [| a1 l IH].
  - intros.
    simpl in H1.
    inversion H.
    subst.
    destruct H0 as [H0 _].
    simpl in H0.
    assert (dQ.(pset) = []) as H_pset_empty. {
      apply Permutation_nil.
      apply Permutation_sym.
      assumption.
    }
    rewrite H_pset_empty.
    simpl.
    lra.
  - intros.
    destruct lQ as [| [r d] lQ'].
    + pose proof Forall2_same_length _ _ _ H as H_same_length.
      assert (a1 :: l = []). {
        apply length_zero_iff_nil.
        rewrite H_same_length.
        auto.
      }
      rewrite H2 in H1.
      simpl in H1.
      destruct H0 as [H0 _].
      simpl in H0.
      assert (dQ.(pset) = []) as H_pset_empty. {
        apply Permutation_nil.
        apply Permutation_sym.
        assumption.
      }
      rewrite H_pset_empty.
      simpl.
      lra.
    + set (dQ'_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) lQ'))).
      set (dQ'_prob := fun Pa => sum (map (fun '(r0, d) => (r0 * d.(prob) Pa)%R) lQ')).
      set (dQ' := {| ProbDistr.pset := dQ'_pset; ProbDistr.prob := dQ'_prob; |}).
      assert (ProbDistr.sum_distr lQ' dQ') as H_sum_dQ'. {
        split; auto.
      }
      inversion H.
      simpl in H1.
      pose proof IH dQ' Q lQ' (sum_r - dA.(prob) a1)%R as H_sum_dQ'_eq.
      specialize (H_sum_dQ'_eq H7 H_sum_dQ').
      assert (sum (map dA.(prob) l) = (dA.(prob) a1 + sum (map dA.(prob) l) - dA.(prob) a1)%R) by lra.
      assert (sum (map dA.(prob) l) = (sum_r - dA.(prob) a1)%R) by lra.
      specialize (H_sum_dQ'_eq H9).
      subst.
      clear H8 H9.
      assert (sum (map dQ'.(prob) dQ'.(pset)) = (sum (map dA.(prob) l))%R) by lra.
      destruct (in_dec eq_dec (Q a1) dQ'.(pset)) as [H_in | H_not_in].
      * assert (Permutation dQ.(pset) dQ'.(pset)). {
          destruct H0 as [H0 _].
          simpl in H0.
          destruct H_sum_dQ' as [H2 _].
          assert (d.(pset) = [Q a1]) by apply H5.
          rewrite H3 in H0.
          pose proof perm_filter_dup_in (concat (map (fun '(_, d) => d.(pset)) lQ')) (Q a1) H_in as H_perm.
          pose proof Permutation_trans.
          specialize (H4 _ _ _ _ H0 H_perm).
          auto.
        }
        assert (dQ.(prob) (Q a1) = dQ'.(prob) (Q a1) + dA.(prob) a1)%R. {
          destruct H0 as [_ Hprob].
          specialize (Hprob (Q a1)).
          simpl in Hprob.
          assert (r = dA.(prob) a1) by apply H5.
          assert (d.(prob) (Q a1) = 1%R) by apply H5.
          rewrite H3, H0 in Hprob.
          destruct H_sum_dQ' as [_ Hprob'].
          specialize (Hprob' (Q a1)).
          rewrite <- Hprob' in Hprob.
          lra.
        }
        rewrite H2.
        assert (forall b, In b dQ'.(pset) -> b <> Q a1 -> dQ.(prob) b = dQ'.(prob) b). {
          intros.
          destruct H0 as [_ Hprob].
          specialize (Hprob b).
          simpl in Hprob.
          destruct H_sum_dQ' as [_ Hprob'].
          specialize (Hprob' b).
          rewrite <- Hprob' in Hprob.
          destruct (eq_dec (Q a1) b) as [? | Hneq].
          - subst.
            contradiction.
          - assert ((forall b : Prop, Q a1 <> b -> d.(prob) b = 0%R)) by apply H5.
            specialize (H0 b).
            pose proof H0 Hneq.
            rewrite H8 in Hprob.
            lra.
        }
        assert (exists Qpset'', Permutation dQ'.(pset) (Q a1 :: Qpset'')) as [Qpset'' ?]. {
          pose proof in_exists_remaining_list_perm dQ'.(pset) (Q a1) H_in as [Qpset'' H_perm].
          exists Qpset''.
          auto.
        }
        rewrite H6.
        simpl.
        rewrite H3.
        assert (forall b, In b Qpset'' -> dQ.(prob) b = dQ'.(prob) b). {
          intros.
          specialize (H4 b).
          assert (In b (Q a1 :: Qpset'')). {right; auto. }
          pose proof Permutation_in.
          apply Permutation_sym in H6.
          specialize (H10 Prop (Q a1 :: Qpset'') dQ'.(pset) b H6 H9).
          specialize (H4 H10).
          apply H4.
          assert (NoDup dQ'.(pset)). {
            pose proof filter_dup_nodup (concat (map (fun '(_, d) => d.(pset)) lQ')) as H_nodup.
            auto.
          }
          pose proof Permutation_NoDup.
          apply Permutation_sym in H6.
          specialize (H12 _ _ _ H6).
          pose proof H12 H11.
          pose proof NoDup_cons_iff.
          specialize (H14 Prop (Q a1) Qpset'') as [H14 _].
          specialize (H14 H13) as [H14 _].
          destruct (eq_dec b (Q a1)) as [? | Hneq].
          - subst.
            contradiction.
          - auto.
        }
        assert (map dQ.(prob) Qpset'' = map dQ'.(prob) Qpset''). {
          apply in_map_eq.
          auto.
        }
        rewrite H9.
        assert (dQ'.(prob) (Q a1) + sum (map dQ'.(prob) Qpset'') = sum (map dQ'.(prob) dQ'.(pset)))%R. {
          assert (Permutation (map dQ'.(prob) dQ'.(pset)) (map dQ'.(prob) (Q a1 :: Qpset''))). {
            apply Permutation_sym.
            apply Permutation_map.
            apply Permutation_sym.
            auto.
          }
          pose proof sum_congr _ _ H10.
          rewrite H11.
          simpl.
          reflexivity.
        }
        lra.
      * assert (Permutation dQ.(pset) ((Q a1) :: dQ'.(pset))). {
          destruct H0 as [H0 _].
          simpl in H0.
          destruct H_sum_dQ' as [H2 _].
          assert (d.(pset) = [Q a1]) by apply H5.
          rewrite H3 in H0.
          pose proof perm_filter_dup_notin (concat (map (fun '(_, d) => d.(pset)) lQ')) (Q a1) H_not_in as H_perm.
          simpl.
          unfold dQ'_pset.
          assert (Permutation dQ.(pset) (filter_dup ((Q a1) :: concat (map (fun '(_, d) => d.(pset)) lQ')))) by auto.
          pose proof Permutation_trans.
          specialize (H6 _ _ _ _ H4 H_perm).
          auto.
        }
        rewrite H2.
        simpl.
        assert (dQ.(prob) (Q a1) = dA.(prob) a1). {
          destruct H0 as [Hpset Hprob].
          specialize (Hprob (Q a1)).
          simpl in Hprob.
          assert (r = dA.(prob) a1) by apply H5.
          assert (d.(prob) (Q a1) = 1%R) by apply H5.
          rewrite H3, H0 in Hprob.
          assert (sum (map (fun '(r, d) => r * d.(prob) (Q a1)) lQ') = 0)%R. {
            pose proof prob_zero_1 lQ' dQ' l dA Q a1 H_sum_dQ' H7 H_not_in as H_prob_zero_1.
            pose proof prob_zero_2 dQ' l dA Q a1 lQ' H_prob_zero_1 as H_prob_zero_2.
            assumption.
          }
          rewrite H4 in Hprob.
          lra.
        }
        rewrite H3.
        assert (forall b, In b dQ'.(pset) -> dQ.(prob) b = dQ'.(prob) b). {
          intros.
          destruct H0 as [_ Hprob].
          specialize (Hprob b).
          simpl in Hprob.
          destruct H_sum_dQ' as [_ Hprob'].
          specialize (Hprob' b).
          rewrite <- Hprob' in Hprob.
          destruct (eq_dec (Q a1) b) as [? | Hneq].
          - subst.
            contradiction.
          - assert ((forall b : Prop, Q a1 <> b -> d.(prob) b = 0%R)) by apply H5.
            specialize (H0 b).
            pose proof H0 Hneq.
            rewrite H6 in Hprob.
            lra.
        }
        assert ((map dQ.(prob) dQ'_pset)%R = map dQ'.(prob) dQ'_pset). {
          apply in_map_eq.
          auto.
        }
        rewrite H6, <- H1.
        simpl.
        lra.
Qed.

Lemma forall2_always:
  forall {A: Type} (dA: Distr A) (P: A -> Prop) (lP_r: list R) (lP_d: list (Distr Prop)) (lP: list (R * Distr Prop)),
    lP_r = map dA.(prob) dA.(pset) ->
    lP_d = map (fun a => {| ProbDistr.pset := [P a]; ProbDistr.prob := fun b => if eq_dec b (P a) then 1%R else 0%R |}) dA.(pset) ->
    lP = combine lP_r lP_d ->
    Forall2
      (fun (a : A) '(r, d0) =>
        r = dA.(prob) a /\
        d0.(pset) = [P a] /\
        d0.(prob) (P a) = 1%R /\
        (forall b : Prop, P a <> b -> d0.(prob) b = 0%R))
      dA.(pset) lP.
Proof.
  intros A dA.
  induction dA.(pset) as [| a l IH].
  - intros.
    subst.
    simpl.
    constructor.
  - intros.
    simpl in H, H0.
    rewrite H, H0 in H1.
    simpl in H1.
    inversion H1.
    constructor.
    + repeat split; auto.
      * simpl.
        destruct (eq_dec (P a) (P a)) as [? | H_neq].
        -- lra.
        -- contradiction.
      * intros.
        simpl.
        destruct (eq_dec b (P a)).
        -- subst.
           contradiction.
        -- reflexivity.
    + specialize (IH P (map dA.(prob) l) 
        (map (fun a : A => {|
          ProbDistr.prob :=
            fun b : Prop => if eq_dec b (P a) then 1%R else 0%R;
          ProbDistr.pset := [P a]
          |}) l) 
        (combine (map dA.(prob) l) (map (fun a : A => {|
          ProbDistr.prob :=
            fun b : Prop => if eq_dec b (P a) then 1%R else 0%R;
          ProbDistr.pset := [P a]
          |}) l))
      ).
      auto.
Qed.

Lemma sum_distr_prob_sum_nonneg:
  forall {A: Type} (la: list A) (dA: Distr A) (dP: Distr Prop) (P: A -> Prop) (lP: list (R * Distr Prop)),
    ProbDistr.legal dA ->
    Forall2
      (fun (a : A) '(r, d0) =>
        r = dA.(prob) a /\
        d0.(pset) = [P a] /\
        d0.(prob) (P a) = 1%R /\
        (forall b : Prop, P a <> b -> d0.(prob) b = 0%R))
      la lP ->
    incl la dA.(pset) ->
    ProbDistr.sum_distr lP dP ->
    (forall a, (sum (map (fun '(r0, d0) => r0 * d0.(prob) (P a)) lP) >= 0)%R).
Proof.
  intros A la.
  induction la as [| a1 l IH].
  - intros.
    pose proof Forall2_same_length _ _ _ H0 as H_same_length.
    assert (lP = []) as H_lP_empty. {
      apply length_zero_iff_nil.
      simpl in H_same_length.
      auto.
    }
    subst.
    simpl.
    lra.
  - intros.
    destruct lP as [| [r d] lP'].
    + inversion H0.
    + inversion H0.
      subst.
      destruct H2 as [Hpset Hprob].
      simpl in Hprob.
      set (dP'_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) lP'))).
      set (dP'_prob := fun Pa => sum (map (fun '(r0, d0) => (r0 * d0.(prob) Pa)%R) lP')).
      set (dP' := {| ProbDistr.pset := dP'_pset; ProbDistr.prob := dP'_prob; |}).
      assert (ProbDistr.sum_distr lP' dP') as H_sum_dP'. {
        split; auto.
      }
      assert (r >= 0)%R. {
        destruct H as [? ? ? ?].
        specialize (legal_nonneg a1).
        assert (r = dA.(prob) a1) by apply H6.
        lra.
      }
      assert (r * d.(prob) (P a1) >= 0)%R. {
        destruct (eq_dec (P a1) (P a1)) as [Heq | Hneq].
        - assert (d.(prob) (P a1) = 1%R) by apply H6.
          rewrite H3.
          lra.
        - contradiction.
      }
      simpl.
      assert (incl l dA.(pset)) as H_incl. {
        pose proof incl_app_inv [a1] l H1 as [_ H_incl].
        auto.
      }
      destruct (eq_dec (P a1) (P a)) as [Heq | Hneq].
      * subst.
        specialize (IH dA dP' P lP' H H8 H_incl H_sum_dP' a1).
        rewrite <- Heq.
        lra.
      * specialize (IH dA dP' P lP' H H8 H_incl H_sum_dP' a).
        assert (forall b : Prop, P a1 <> b -> d.(prob) b = 0%R) by apply H6.
        specialize (H4 (P a) Hneq).
        rewrite H4.
        lra.
Qed.
        
(* Lemma sum_distr_prob_nonneg:
  forall {A: Type} (dA: Distr A) (dP: Distr Prop) (P: A -> Prop) (lP: list (R * Distr Prop)),
    ProbDistr.legal dA ->
    Forall2
      (fun (a : A) '(r, d0) =>
      r = dA.(prob) a /\
      d0.(pset) = [P a] /\
      d0.(prob) (P a) = 1%R /\
      (forall b : Prop, P a <> b -> d0.(prob) b = 0%R))
    dA.(pset) lP ->
    ProbDistr.sum_distr lP dP ->
    (forall a, In a dA.(pset) -> dP.(prob) (P a) >= 0)%R.
Proof.
  intros A dA.
  induction dA.(pset) as [| a1 l IH].
  - intros.
    contradiction.
  - intros.
    destruct lP as [| [r d] lP'].
    + inversion H0.
    + inversion H0.
      subst.
      destruct H1 as [Hpset Hprob].
      simpl in Hprob.
      set (dP'_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) lP'))).
      set (dP'_prob := fun Pa => sum (map (fun '(r0, d) => (r0 * d.(prob) Pa)%R) lP')).
      set (dP' := {| ProbDistr.pset := dP'_pset; ProbDistr.prob := dP'_prob; |}).
      assert (ProbDistr.sum_distr lP' dP') as H_sum_dP'. {
        split; auto.
      }
      assert (r >= 0)%R. {
        destruct H as [? ? ? ?].
        specialize (legal_nonneg a1).
        assert (r = dA.(prob) a1) by apply H6.
        lra.
      }
      assert (r * d.(prob) (P a) >= 0)%R. {
        destruct (eq_dec (P a) (P a1)) as [Heq | Hneq].
        - assert (d.(prob) (P a1) = 1%R) by apply H6.
          rewrite <- Heq in H3.
          rewrite H3.
          lra.
        - assert (d.(prob) (P a) = 0%R). {
            apply H6.
            auto.
          }
          rewrite H3.
          lra.
      }
      destruct H2.
      * subst a.
        specialize (Hprob (P a1)).
        assert (r = dA.(prob) a1) by apply H6.
        assert (d.(prob) (P a1) = 1%R) by apply H6.
        rewrite H2, H4 in Hprob.
        assert (sum (map (fun '(r, d) => r * d.(prob) (P a1)) lP') >= 0)%R. {
          
          apply sum_distr_prob_sum_nonneg with (dA := dA) (dP := dP') (P := P) (lP := lP'); auto.
        }
        rewrite Hprob, <- H2.
        lra.
      * specialize (IH dP' P lP' H H8 H_sum_dP' a H2).
        unfold dP' in IH.
        simpl in IH.
        unfold dP'_prob in IH.
        specialize (Hprob (P a)).
        
        lra.
  Admitted. *)

Lemma split_zero_and_pos_from_nonneg_list:
  forall {A: Type} (l: list A) (f: A -> R) (r: R),
    (forall a, In a l -> f a >= 0)%R ->
    sum (map f l) = r ->
    exists zero_list pos_list, Permutation l (zero_list ++ pos_list) /\
      (forall a, In a zero_list -> f a = 0)%R /\
      (forall a, In a pos_list -> f a > 0)%R /\ 
      sum (map f pos_list) = r.
Proof.
  induction l as [| a l IH].
  - intros.
    exists [], [].
    simpl.
    repeat split.
    + apply Permutation_refl.
    + intros.
      contradiction.
    + intros.
      contradiction.
    + simpl in H0.
      lra.
  - intros.
    assert (In a (a :: l)) by (left; auto).
    pose proof H a H1.
    clear H1.
    assert (forall a : A, In a l -> (f a >= 0)%R). {
      intros.
      apply H.
      right; auto.
    }
    destruct (Req_dec 0 (f a)).
    + simpl in H0.
      assert (sum (map f l) = r) by lra.
      specialize (IH f r H1 H4) as [l0 [lpos [Hperm [Hzero [Hpos Hsum]]]]].
      exists (a :: l0), lpos.
      repeat split.
      * apply (perm_skip a Hperm).
      * intros.
        destruct (eq_dec a a0).
        -- subst.
           auto.
        -- apply Hzero.
           destruct H5.
            ++ subst.
               contradiction.
            ++ auto.
      * intros.
        apply Hpos.
        auto.
      * auto.
    + assert (sum (map f l) = (r - f a)%R). {
        simpl in H0.
        lra.
      }
      specialize (IH f (r - f a)%R H1 H4) as [l0 [lpos [Hperm [Hzero [Hpos Hsum]]]]].
      exists l0, (a :: lpos).
      repeat split.
      * apply (Permutation_cons_app l0 lpos a Hperm).
      * intros.
        apply Hzero.
        auto.
      * intros.
        destruct H5.
        -- subst.
           lra.
        -- apply Hpos.
           auto.
      * simpl.
        lra.
Qed.

Lemma nonneg_sublist_sum_le:
  forall {A: Type} (l: list A) (f: A -> R) (r: R) (subl: list A),
    (forall a, In a l -> f a >= 0)%R ->
    sum (map f l) = r ->
    incl subl l ->
    (sum (map f subl) <= r)%R.
Admitted.

Lemma nonneg_sublist_sum_ge:
  forall {A: Type} (l: list A) (f: A -> R) (r: R) (subl: list A),
    (forall a, In a l -> f a >= 0)%R ->
    sum (map f subl) = r ->
    incl subl l ->
    (sum (map f l) >= r)%R.
Admitted.

Lemma sumup_incl:
  forall {A: Type} (zero_list pos_list l: list A) (f: A -> R) (r: R),
    Permutation l (zero_list ++ pos_list) ->
    (forall a, In a zero_list -> f a = 0)%R ->
    (forall a, In a pos_list -> f a > 0)%R ->
    sum (map f pos_list) = r ->
    (r >= 0)%R ->
    (forall subl, incl subl l -> (sum (map f subl) = r)%R -> incl pos_list subl).
Proof.
  induction pos_list as [| a pos_list' IH].
  - intros.
    apply incl_nil_l.
  - intros.
    assert (Permutation (zero_list ++ pos_list') (zero_list ++ pos_list')) by apply Permutation_refl.
    assert (forall a : A, In a pos_list' -> (f a > 0)%R). {
      intros.
      apply H1.
      right; auto.
    }
    assert (sum (map f pos_list') = (r - f a)%R). {
      simpl in H2.
      lra.
    }
    assert ((r - f a >= 0)%R). {
      rewrite <- H8.
      clear - H7.
      induction pos_list' as [| a' pos_list'' IH'].
      - simpl.
        lra.
      - simpl.
        assert (f a' > 0)%R. {
          specialize (H7 a').
          apply H7.
          left; auto.
        }
        assert (forall a : A, In a pos_list'' -> (f a > 0)%R). {
          intros.
          apply H7.
          right; auto.
        }
        specialize (IH' H0).
        lra.
    }
    specialize (IH (zero_list ++ pos_list') f (r - (f a))%R H6 H0 H7 H8 H9).
    destruct (in_dec eq_dec a subl) as [Hin | Hnotin].
    + pose proof in_split a subl Hin as [subl1 [subl2 ?]].
  Admitted. 
    
Lemma always_conseq_1:
  forall {A: Type} (dA: Distr A) (dP: Distr Prop) (P: A -> Prop) (lP: list (R * Distr Prop)),
    (forall a, In a dA.(pset) -> (dA.(prob) a >= 0)%R) ->
    Forall2
       (fun (a : A) '(r, d0) =>
        r = dA.(prob) a /\
        d0.(pset) = [P a] /\
        d0.(prob) (P a) = 1%R /\
        (forall b : Prop, P a <> b -> d0.(prob) b = 0%R)) dA.(pset) lP ->
    ProbDistr.sum_distr lP dP ->
    (forall pa, In pa dP.(pset) -> (dP.(prob) pa >= 0)%R).
Proof.
  intros A dA.
  induction dA.(pset) as [| a1 l IH].
  + intros.
    pose proof Forall2_same_length _ _ _ H0 as H_same_length.
    assert (lP = []) as H_lP_empty. {
      apply length_zero_iff_nil.
      simpl in H_same_length.
      auto.
    }
    destruct H1 as [H1 _].
    rewrite H_lP_empty in H1.
    simpl in H1.
    apply Permutation_sym in H1.
    apply Permutation_nil in H1.
    rewrite H1 in H2.
    contradiction.
  + intros.
    destruct lP as [| [r d] lP'].
    - inversion H0.
    - inversion H0.
      subst.
      destruct H1 as [Hpset Hprob].
      simpl in Hprob.
      set (dP'_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) lP'))).
      set (dP'_prob := fun Pa => sum (map (fun '(r0, d) => (r0 * d.(prob) Pa)%R) lP')).
      set (dP' := {| ProbDistr.pset := dP'_pset; ProbDistr.prob := dP'_prob; |}).
      assert (ProbDistr.sum_distr lP' dP') as H_sum_dP'. {
        split; auto.
      }
      assert (forall a : A, In a l -> (dA.(prob) a >= 0)%R). {
        intros.
        apply H.
        right; auto.
      }
      specialize (IH dP' P lP' H1 H8 H_sum_dP' pa).
      assert (r = dA.(prob) a1) by apply H6.
      assert (r >= 0)%R. {
        assert (In a1 (a1 :: l)). {
          left; auto.
        }
        specialize (H a1 H4).
        rewrite H3.
        auto.
      }
      destruct (eq_dec pa (P a1)) as [Heq | Hneq].
      * admit.
      * admit.
Admitted. 

Theorem Always_conseq: forall {A: Type} (P Q: A -> Prop),
  (forall a, P a -> Q a) ->
  (forall c, Always c P -> Always c Q).
Proof.
  unfold Always.
  unfold Hoare.
  unfold ProbMonad.compute_pr.
  simpl.
  unfold ProbMonad.__bind.
  unfold ProbMonad.__ret.
  unfold ProbDistr.is_det.
  sets_unfold.
  intros A P Q Himp f ? rQ ?.
  destruct H0 as [dQ [Hd ?]].
  destruct Hd as [dA [lQ [Hda_in_f [Hforall2 H_sum_distr]]]]. 

  set (lP_r := map dA.(prob) dA.(pset)).
  set (lP_d := map (fun a => {| ProbDistr.pset := [P a]; ProbDistr.prob := fun b => if eq_dec b (P a) then 1%R else 0%R |}) dA.(pset)).
  set (lP := combine lP_r lP_d).

  (* pset 为 dA.pset 的每个元素 a 映射到 P a*)
  set (dP_pset := filter_dup (map (fun a => P a) dA.(pset))).
  (* prob 为一个 Prop -> R 的函数，对每个 P a，dP_prob (P a) = dA.(prob) (a) *)
  set (dP_prob := fun Pa => sum (map (fun '(r0, d) => (r0 * d.(prob) Pa)%R) lP)).
  (* dP 为一个 Distr Prop，pset 为 dP_pset，prob 为 dP_prob *)
  set (dP := {| ProbDistr.pset := dP_pset; ProbDistr.prob := dP_prob |}).

  pose proof ProbDistr_compute_pr_exists dP as [rP ?].
  specialize (H rP).
    assert (ProbDistr.sum_distr lP dP) as H_sum_dP. {
    split; auto.
    assert (map (fun '(_, d) => d.(pset)) lP = map (fun d => d.(pset)) lP_d) as H_map_eq. {
        clear Hforall2 H1.
        induction dA.(pset) as [| a l IH].
        + simpl.
          reflexivity.
        + simpl.
          rewrite IH.
          reflexivity.
      }
      rewrite H_map_eq.
      clear H_map_eq.
      simpl.
      unfold lP_d, dP_pset.
      rewrite map_map.
      simpl.
      assert (concat (map (fun x : A => [P x]) dA.(pset)) = map (fun a : A => P a) dA.(pset)). {
        clear Hforall2 H1.
        induction dA.(pset) as [| a l IH].
        + simpl.
          reflexivity.
        + simpl.
          rewrite IH.
          reflexivity.
      }
      rewrite H2.
      auto.
  }
  assert (Forall2
    (fun (a : A) '(r, d0) =>
    r = dA.(prob) a /\
    d0.(pset) = [P a] /\
    d0.(prob) (P a) = 1%R /\
    (forall b : Prop, P a <> b -> d0.(prob) b = 0%R)) dA.(pset) lP). {
    pose proof forall2_always dA P lP_r lP_d lP as H_forall2.
    assert (lP_r = map dA.(prob) dA.(pset)) by auto.
    assert (lP_d = map (fun a => {| ProbDistr.pset := [P a]; ProbDistr.prob := fun b => if eq_dec b (P a) then 1%R else 0%R |}) dA.(pset)) by auto.
    assert (lP = combine lP_r lP_d) by auto.
    specialize (H_forall2 H2 H3 H4).
    auto.
  }
  assert (
    exists d : Distr Prop,
       (exists (s1 : Distr A) (l : list (R * Distr Prop)),
          s1 ∈ f.(distr) /\
          Forall2
            (fun (a : A) '(r, d0) =>
             r = s1.(prob) a /\
             d0.(pset) = [P a] /\ d0.(prob) (P a) = 1%R /\ (forall b : Prop, P a <> b -> d0.(prob) b = 0%R))
            s1.(pset) l /\ ProbDistr.sum_distr l d) /\ ProbDistr.compute_pr d rP
  ). {
    exists dP.
    split; auto.
    exists dA, lP.
    split; auto.
  }
  specialize (H H3).
  clear H3.

  (* Prove rQ = 1 *)
  (* sum prob A = 1 *)
  pose proof f.(legal).(Legal_legal) dA Hda_in_f as H_legal_f.
  destruct H_legal_f as [_ _ _ H_prob_1_dA].
  unfold sum_prob in H_prob_1_dA.
  unfold ProbDistr.compute_pr in *.
  destruct H0 as [ltrueQ [HtrueQ HsumQ]].
  destruct H1 as [ltrueP [HtrueP HsumP]].
  assert (sum (map dP.(prob) dP.(pset)) = 1%R) as HsumPset1. {
    apply sum_prob1 with (dA := dA) (dQ := dP) (Q := P) (lQ := lP); auto.
  }
  assert (sum (map dQ.(prob) dQ.(pset)) = 1%R) as HsumQset1. {
    apply sum_prob1 with (dA := dA) (dQ := dQ) (Q := Q) (lQ := lQ); auto.
  } 
  pose proof f.(legal).(Legal_legal) dA Hda_in_f as H_legal_f.
  destruct H_legal_f as [_ ? _ _].
  assert (forall a, In a dA.(pset) -> (dA.(prob) a >= 0)%R) as Hproba. {
    intros.
    apply legal_nonneg.
  }
  pose proof always_conseq_1 dA dP P lP Hproba H2 H_sum_dP as HnonnegP.
  pose proof always_conseq_1 dA dQ Q lQ Hproba Hforall2 H_sum_distr as HnonnegQ.
  pose proof split_zero_and_pos_from_nonneg_list dQ.(pset) dQ.(prob) 1%R HnonnegQ HsumQset1 as [lQzero [lQpos [HpermQ [HzeroQ [HposQ HsumposQ]]]]].
  pose proof split_zero_and_pos_from_nonneg_list dP.(pset) dP.(prob) 1%R HnonnegP HsumPset1 as [lPzero [lPpos [HpermP [HzeroP [HposP HsumposP]]]]].

  assert (incl lPpos ltrueP) as H_inclP. {
    apply sumup_incl with (zero_list := lPzero) (pos_list := lPpos) (l := dP.(pset)) (f := dP.(prob)) (r := 1%R); auto.
    + lra.
    + apply incl_Forall_in_iff.
      apply Forall_forall.
      intros.
      specialize (HtrueP x) as [? _].
      specialize (H1 H0) as [? _].
      assumption.
    + destruct HsumP as [HsumP' _].
      unfold sum_prob in HsumP'.
      rewrite HsumP'.
      assumption.
  }
  assert (forall pa, In pa lPpos -> pa) as H_postrueP. {
    intros.
    apply H_inclP in H0.
    specialize (HtrueP pa) as [? _].
    specialize (H1 H0) as [_ ?].
    assumption.
  }
  assert (forall qa, In qa lQpos -> qa) as H_postrueQ. {
    intros.
    admit.
  }
  assert (incl lQpos ltrueQ) as H_inclQ. {
    apply incl_Forall_in_iff.
    apply Forall_forall.
    intros.
    assert (In x (lQzero ++ lQpos)). {
      apply in_or_app.
      right; auto.
    }
    apply Permutation_sym in HpermQ.
    pose proof Permutation_in x HpermQ H1.
    specialize (H_postrueQ x H0).
    destruct (HtrueQ x) as [_ ?].
    apply H4.
    auto.
  } 
  assert ((sum (map dQ.(prob) ltrueQ) <= 1)%R). {
    assert (incl ltrueQ dQ.(pset)). {
      apply incl_Forall_in_iff.
      apply Forall_forall.
      intros.
      specialize (HtrueQ x) as [? _].
      specialize (H1 H0) as [? _].
      assumption.
    }
    pose proof nonneg_sublist_sum_le dQ.(pset) dQ.(prob) 1%R ltrueQ HnonnegQ HsumQset1 H0.
    assumption.
  }
  assert ((sum (map dQ.(prob) ltrueQ) >= 1)%R). {
    assert (forall a : Prop, In a ltrueQ -> (dQ.(prob) a >= 0)%R). {
      intros.
      destruct (HtrueQ a) as [? _].
      specialize (H3 H1) as [? _].
      specialize (HnonnegQ a H3).
      assumption.
    }
    pose proof nonneg_sublist_sum_ge ltrueQ dQ.(prob) 1%R lQpos H1 HsumposQ H_inclQ.
    assumption.
  }
  destruct HsumQ as [HsumQ' _].
  unfold sum_prob in HsumQ'.
  rewrite <- HsumQ'.
  lra.
Admitted.

Theorem Always_bind_ret {A B: Type}:
  forall (c2: A -> ProbMonad.M B)
         (f: A -> B)
         (P: B -> Prop),
    (forall a, c2 a = ret (f a)) ->
    (forall c1, Always c1 (fun a => P (f a)) <-> Always (a <- c1;; c2 a) P).
Admitted. (** Level 1 *)

Theorem compute_pr_exists: forall f, exists r, ProbMonad.compute_pr f r.
Proof.
  intros.
  unfold ProbMonad.compute_pr.
  pose proof f.(legal).(Legal_exists) as [d ?].
  pose proof ProbDistr_compute_pr_exists d as [r ?].
  exists r, d.
  tauto.
Qed.

#[export] Instance ProbMonad_imply_event_refl:
  Reflexive ProbMonad.imply_event.
Proof. (** Level 2 *)
  unfold Reflexive.
  unfold ProbMonad.imply_event.
  intros.
  assert (exists d, d ∈ x.(distr)) as [d ?].
  {
    apply x.(legal).(Legal_exists).
  }
  exists d, d.
  repeat split; auto.
  apply ProbDistr_imply_event_refl.
Qed.
  
Theorem ProbMonad_imply_event_refl_setoid:
  forall d1 d2, ProbMonad.equiv_event d1 d2 -> ProbMonad.imply_event d1 d2.
Proof. (** Level 2 *)
  intros.
  unfold ProbMonad.equiv_event, ProbMonad.imply_event in *.
  destruct H as [r1 [r2 [? [? ?]]]].
  exists r1, r2.
  repeat split; auto.
  rewrite H1.
  apply ProbDistr_imply_event_refl.
Qed.

#[export] Instance ProbMonad_equiv_equiv {A: Type}:
  Equivalence (@ProbMonad.equiv A).
Proof.
  unfold ProbMonad.equiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

Lemma ProbDistr_equiv_equiv_event:
  forall d1 d2, ProbDistr.equiv d1 d2 -> ProbDistr.equiv_event d1 d2.
Proof.
  intros.
  unfold ProbDistr.equiv, ProbDistr.equiv_event in *.
  destruct H.
  pose proof ProbDistr_compute_pr_exists as Hex.
  pose proof Hex d1 as [r1 ?].
  pose proof Hex d2 as [r2 ?].
  exists r1, r2.
  repeat split; auto.
  clear Hex.
  unfold ProbDistr.compute_pr in *.
  destruct H1 as [l1 [H11 [H12 H13]]].
  destruct H2 as [l2 [H21 [H22 H23]]].
  assert (forall P, In P d1.(pset) /\ P <-> In P d2.(pset) /\ P) as H_eq_pset. {
    split; intros.  
    + destruct H1 as [? ?].
      split; auto.
      apply Permutation_in with (l := d1.(pset)); auto.
    + destruct H1 as [? ?].
      split; auto.
      apply Permutation_sym in H0.
      apply Permutation_in with (l := d2.(pset)); auto.   
  }
  assert (forall P, In P l1 <-> In P l2). {
    intros.
    split; intros.
    + specialize (H11 P).
      specialize (H21 P).
      specialize (H_eq_pset P).
      tauto.
    + specialize (H11 P).
      specialize (H21 P).
      specialize (H_eq_pset P).
      tauto.
  }
  destruct H12, H22.
  unfold sum_prob.
  assert (Permutation l1 l2). {
    pose proof NoDup_Permutation H13 H23 H1.
    assumption.
  }
  assert (d1.(prob) = d2.(prob)) as H_eq_d. {
    apply functional_extensionality.
    intros.
    specialize (H x).
    assumption.
  }
  rewrite <- H_eq_d.
  apply sum_congr.
  apply Permutation_map'.
  assumption.
Qed.
  
#[export] Instance ProbMonad_imply_event_trans:
  Transitive ProbMonad.imply_event.
Proof. (** Level 2 *)
  unfold Transitive, ProbMonad.imply_event.
  intros x y z.
  intros [dx [dy [Hx [Hy H_imp_xy]]]] [dy' [dz [Hy' [Hz H_imp_yz]]]].
  exists dx, dz.
  repeat split; auto.
  assert (ProbDistr.equiv dy dy') as H_eq_dy_dy'. {
    pose proof y.(legal).(Legal_unique) as H_unique_y.
    pose proof H_unique_y dy dy' Hy Hy'.
    assumption.    
  }
  apply ProbDistr_equiv_equiv_event in H_eq_dy_dy'.
  apply ProbDistr_imply_event_refl_setoid in H_eq_dy_dy'.
  pose proof ProbDistr_imply_event_trans _ _ _ H_imp_xy H_eq_dy_dy'.
  pose proof ProbDistr_imply_event_trans _ _ _ H H_imp_yz.
  assumption.
Qed.
  

#[export] Instance ProbMonad_equiv_event_equiv:
  Equivalence ProbMonad.equiv_event.
Proof. (** Level 2 *)
  unfold ProbMonad.equiv_event.
  split.
  - unfold Reflexive.
    intros.
    assert (exists d, d ∈ x.(distr)) as [d ?].
    {
      apply x.(legal).(Legal_exists).
    }
    exists d, d.
    repeat split; auto.
    reflexivity.
  - unfold Symmetric.
    intros.
    destruct H as [d1 [d2 [H1 [H2 Heq]]]].
    exists d2, d1.
    repeat split; auto.
    symmetry.
    auto.
  - unfold Transitive.
    intros x y z.
    intros [d1 [d2 [H1 [H2 Heq]]]] [d2' [d3 [H2' [H3 Heq']]]].
    exists d1, d3.
    repeat split; auto.
    assert (ProbDistr.equiv d2 d2') as H_eq_dy_dy'. {
      pose proof y.(legal).(Legal_unique) as H_unique_y.
      pose proof H_unique_y d2 d2' H2 H2'.
      assumption.    
    }
    apply ProbDistr_equiv_equiv_event in H_eq_dy_dy'.
    transitivity d2; auto.
    transitivity d2'; auto.
Qed.

#[export] Instance ProbMonad_imply_event_congr:
  Proper (ProbMonad.equiv_event ==>
          ProbMonad.equiv_event ==> iff) ProbMonad.imply_event.
Proof. (** Level 2 *)
  unfold Proper, respectful.
  intros x y H x0 y0 H0.
  split; intros.
  - apply symmetry in H.
    apply ProbMonad_imply_event_refl_setoid in H.
    apply ProbMonad_imply_event_refl_setoid in H0.
    transitivity x; auto.
    transitivity x0; auto.
  - apply ProbMonad_imply_event_refl_setoid in H.
    apply symmetry in H0.
    apply ProbMonad_imply_event_refl_setoid in H0.
    transitivity y; auto.
    transitivity y0; auto.
Qed.  

#[export] Instance compute_pr_congr:
  Proper (ProbMonad.equiv_event ==> Sets.equiv) ProbMonad.compute_pr.
Proof. (** Level 2 *)
  unfold Proper, respectful.
  intros x y H.
  destruct H as [d1 [d2 [H1 [H2 Heq]]]].
  sets_unfold.
  unfold ProbMonad.compute_pr.
  intros a.
  split.
  - intros Ha.
    destruct Ha as [d [Hd Hpr]].
    exists d2.
    split; auto.
    pose proof x.(legal).(Legal_unique) as H_unique_x.
    pose proof H_unique_x d d1 Hd H1.
    apply ProbDistr_equiv_equiv_event in H.
    assert (Sets.equiv (ProbDistr.compute_pr d) (ProbDistr.compute_pr d2)) as Hpr2. {
      apply ProbDistr_compute_pr_congr.
      transitivity d1; auto.
    }
    sets_unfold in Hpr2.
    specialize (Hpr2 a).
    tauto.  
  - intros Ha.
    destruct Ha as [d [Hd Hpr]].
    exists d1.
    split; auto.
    pose proof y.(legal).(Legal_unique) as H_unique_y.
    pose proof H_unique_y d d2 Hd H2.
    apply ProbDistr_equiv_equiv_event in H.
    assert (Sets.equiv (ProbDistr.compute_pr d) (ProbDistr.compute_pr d1)) as Hpr1. {
      apply ProbDistr_compute_pr_congr.
      apply symmetry in Heq.
      transitivity d2; auto.
    }
    sets_unfold in Hpr1.
    specialize (Hpr1 a).
    tauto.
Qed.

Theorem compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbMonad.compute_pr f1 r1 ->
    ProbMonad.compute_pr f2 r2 ->
    ProbMonad.imply_event f1 f2 ->
    (r1 <= r2)%R.
Proof.
  intros f1 f2 r1 r2 H1 H2 H_imp.
  destruct H_imp as [d1 [d2 [Hd1 [Hd2 H_imp]]]].
  unfold ProbMonad.compute_pr in *.
  destruct H1 as [d1' [Hd1' Hpr1]].
  destruct H2 as [d2' [Hd2' Hpr2]].
  pose proof f1.(legal).(Legal_unique) as H_unique_f1.
  specialize (H_unique_f1 d1 d1' Hd1 Hd1').
  apply ProbDistr_equiv_equiv_event in H_unique_f1.
  pose proof f2.(legal).(Legal_unique) as H_unique_f2.
  specialize (H_unique_f2 d2 d2' Hd2 Hd2').
  apply ProbDistr_equiv_equiv_event in H_unique_f2.
  apply symmetry in H_unique_f1.
  apply ProbDistr_imply_event_refl_setoid in H_unique_f1.
  apply ProbDistr_imply_event_refl_setoid in H_unique_f2.
  assert (ProbDistr.imply_event d1' d2') as H_imp_d1'_d2'. {
    transitivity d1; auto.
    transitivity d2; auto.
  }
  pose proof ProbDistr_compute_pr_mono.
  specialize (H d1' d2' r1 r2 Hpr1 Hpr2 H_imp_d1'_d2').
  assumption.
Qed.

#[export] Instance ProbMonad_bind_congr (A B: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv ==>
          ProbMonad.equiv)
    (@bind _ ProbMonad A B).
Proof. (** Level 2 *)    
  unfold Proper, pointwise_relation, respectful.
  unfold ProbMonad.equiv in *.
  sets_unfold.
  simpl.
  intros fx fy H f g H0.
  unfold ProbMonad.__bind.
  split.
  + intros.
    destruct H1 as [d [l [Hd_in [Hforall2 H_sum_distr]]]].
    exists d, l.
    split; auto.
    - apply H; auto.
    - split; auto.
      clear H_sum_distr.
      induction Hforall2.
      * constructor.
      * destruct y.
        constructor.
        -- split.
            ++ apply H1.
            ++ apply H0, H1. 
        -- apply IHHforall2.
  + intros.
    destruct H1 as [d [l [Hd_in [Hforall2 H_sum_distr]]]].
    exists d, l.
    split.
    - apply H; auto.
    - split.
      2: auto.
      clear H_sum_distr.
      induction Hforall2.
      * constructor.
      * destruct y.
        constructor.
        -- split.
            ++ apply H1.
            ++ apply H0, H1. 
        -- apply IHHforall2.
Qed. 
  
Lemma forall_to_forall2:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    (forall a b, In (a, b) (combine l1 l2) -> f a b) ->
    length l1 = length l2 -> 
      Forall2 f l1 l2.
Proof.
  intros A B l1 l2 f.
  revert l2.
  induction l1 as [|a l1 IH]; intros l2 H Hlen.
  - destruct l2.
    + constructor.
    + simpl in Hlen. inversion Hlen.
  - destruct l2 as [|b l2].
    + simpl in Hlen. inversion Hlen.
    + simpl in Hlen. inversion Hlen.
      constructor.
      * apply H.
        simpl. left. reflexivity.
      * apply IH; auto.
        intros.
        apply H.
        simpl. right. auto.
Qed.

Lemma pair_eq_inversion : forall (A B : Type) (a a0 : A) (b b0 : B),
  (a, b) = (a0, b0) -> a = a0 /\ b = b0.
Proof.
  intros.
  injection H.
  auto.
Qed.

Require Import Coq.Logic.IndefiniteDescription.

Lemma exists_d_in_l:
  forall {A: Type} (dA: Distr A) (f: A -> ProbMonad.M Prop) (g: A -> ProbMonad.M Prop),
    (forall a, In a dA.(pset) -> (exists d1 d2 : Distr Prop,
      (f a).(distr) d1 /\ (g a).(distr) d2 /\ ProbDistr.imply_event d1 d2)) ->
        exists list_d1 list_d2, 
          Forall2 (fun a d => (f a).(distr) d) dA.(pset) list_d1 /\
          Forall2 (fun a d => (g a).(distr) d) dA.(pset) list_d2 /\
          Forall2 (fun d1 d2 => ProbDistr.imply_event d1 d2) list_d1 list_d2.
Proof.
  intros.
  induction dA.(pset) as [|a l].
  - exists nil, nil.
    repeat constructor.
  - destruct IHl as [list_d1 [list_d2 [H1 [H2 H3]]]].
    + intros.
      apply H.
      simpl. right. auto.
    + assert (exists d1 d2, (f a).(distr) d1 /\ (g a).(distr) d2 /\ ProbDistr.imply_event d1 d2) as Hex. {
        apply H.
        simpl. left. auto.
      }
      destruct Hex as [d1 [d2 [Hd1 [Hd2 H_imp]]]].
      exists (d1 :: list_d1), (d2 :: list_d2).
      repeat split.
      * constructor; auto.
      * constructor; auto.
      * constructor; auto.
Qed.
    
Lemma combine_rd:
  forall {A: Type} (list_r: list R) (list_d: list (Distr Prop)) (dA: Distr A) (f: A -> ProbMonad.M Prop),
    list_r = map dA.(prob) dA.(pset) ->
    Forall2 (fun (a : A) (d : Distr Prop) => (f a).(distr) d) dA.(pset) list_d -> 
    Forall2 (fun (a : A) '(r, d) => r = dA.(prob) a /\ (f a).(distr) d) dA.(pset) (combine list_r list_d).
Proof.
  intros.
  induction H0.
  - assert (list_r = nil) as Hnil. {
      auto.
    }
    subst.
    constructor.
  - simpl in H.
Admitted.

Lemma exists_lx_ly:
  forall {A: Type} (dA: Distr A) (f : A -> ProbMonad.M Prop) (g : A -> ProbMonad.M Prop),
  (forall a : A,
    exists d1 d2 : Distr Prop,
      (f a).(distr) d1 /\
      (g a).(distr) d2 /\ ProbDistr.imply_event d1 d2) ->
    exists lx ly,
      Forall2 (fun (a : A) '(r, d) => r = dA.(prob) a /\ (f a).(distr) d) dA.(pset) lx /\
      Forall2 (fun (a : A) '(r, d) => r = dA.(prob) a /\ (g a).(distr) d) dA.(pset) ly /\
      Forall2 (fun '(rx, dx) '(ry, dy) => rx = ry /\ ProbDistr.imply_event dx dy) lx ly.
Proof.
  intros.
  set (list_r := map dA.(prob) dA.(pset)).
  assert (
    forall a : A, In a dA.(pset) ->
    exists d1 d2 : Distr Prop,
      (f a).(distr) d1 /\
      (g a).(distr) d2 /\ ProbDistr.imply_event d1 d2) as H'. {
    intros.
    apply H.
  }
  pose proof exists_d_in_l dA f g H' as [list_d_x [list_d_y [Hldx [Hldy H_d_imp]]]].
  exists (combine list_r list_d_x), (combine list_r list_d_y).
  repeat split.
  - apply combine_rd; auto.
  - apply combine_rd; auto.
  - admit.
Admitted.

Lemma sum_distr_imply_imply:
  forall dx dy lx ly,
    ProbDistr.sum_distr lx dx ->
    ProbDistr.sum_distr ly dy ->
    Forall2 (fun '(rx, dx) '(ry, dy) => rx = ry /\ ProbDistr.imply_event dx dy) lx ly ->
    ProbDistr.imply_event dx dy.
Proof.
  intros.
  destruct H as [? ? ].
  destruct H0 as [? ?].
Admitted.

Lemma exists_dp_based_on_l:
  forall {A: Type} (dA: Distr A) (f : A -> ProbMonad.M Prop) (g : A -> ProbMonad.M Prop) (lx: list (R * Distr Prop)) (ly: list (R * Distr Prop)),
    Forall2 (fun (a : A) '(r, d) => r = dA.(prob) a /\ (f a).(distr) d) dA.(pset) lx ->
    Forall2 (fun (a : A) '(r, d) => r = dA.(prob) a /\ (g a).(distr) d) dA.(pset) ly ->
    Forall2 (fun '(rx, dx) '(ry, dy) => rx = ry /\ ProbDistr.imply_event dx dy) lx ly ->
    exists dPx dPy,
      ProbDistr.sum_distr lx dPx /\
      ProbDistr.sum_distr ly dPy /\
      ProbDistr.imply_event dPx dPy.
Proof.
  intros.
  set (x_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) lx))).
  set (y_pset := filter_dup (concat (map (fun '(_, d) => d.(pset)) ly))).
  set (x_prob := fun a => sum (map (fun '(r, d) => r * d.(prob) a)%R lx)).
  set (y_prob := fun a => sum (map (fun '(r, d) => r * d.(prob) a)%R ly)).
  set (dPx := {| ProbDistr.pset := x_pset; ProbDistr.prob := x_prob; |}).
  set (dPy := {| ProbDistr.pset := y_pset; ProbDistr.prob := y_prob; |}).
  exists dPx, dPy.
  assert (ProbDistr.sum_distr lx dPx) as H_sum_lx. {
    repeat split; auto.
  }
  assert (ProbDistr.sum_distr ly dPy) as H_sum_ly. {
    repeat split; auto.
  }
  repeat split; auto.
  pose proof sum_distr_imply_imply dPx dPy lx ly H_sum_lx H_sum_ly H1 as H_imp_dPx_dPy.
  assumption.
Qed.

#[export] Instance ProbMonad_bind_mono_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.imply_event ==>
          ProbMonad.imply_event)
    (@bind _ ProbMonad A Prop).
Proof.
  unfold Proper, pointwise_relation, respectful.
  unfold ProbMonad.equiv, ProbMonad.imply_event in *.
  sets_unfold.
  intros x y H f g H0.
  pose proof (x <- x;; f x).(legal).(Legal_exists) as [dx Hdx].
  pose proof (x <- y;; g x).(legal).(Legal_exists) as [dy Hdy].
  exists dx, dy.
  repeat split; auto.
  sets_unfold in Hdx.
  sets_unfold in Hdy.
  simpl in *.
  unfold ProbMonad.__bind in *.
  destruct Hdx as [dA_x [lx [Hdx [Hlx H_sum_lx]]]].
  destruct Hdy as [dA_y [ly [Hdy [Hly H_sum_ly]]]].
Admitted.
(* 
Proof. 
  unfold Proper, pointwise_relation, respectful.
  unfold ProbMonad.equiv, ProbMonad.imply_event in *.
  sets_unfold.
  intros x y H f g H0.
  simpl.
  unfold ProbMonad.__bind.
  sets_unfold.
  pose proof x.(legal).(Legal_exists) as [dA_x Hdx].
  pose proof y.(legal).(Legal_exists) as [dA_y Hdy].
  pose proof exists_lx_ly dA_x f g H0 as [lx [ly [Hlx [Hly H_imp]]]].
  pose proof exists_dp_based_on_l dA_x f g lx ly Hlx Hly H_imp as [dPx [dPy [H_sum_lx [H_sum_ly H_imp_dPx_dPy]]]].
  exists dPx, dPy.
  repeat split; auto.
  - exists dA_x, lx.
    split; auto.
  - exists dA_x, ly.
    split; auto.
    apply (H dA_x).
    auto.
Qed. *)

(* 
Proof. 
  unfold Proper, pointwise_relation, respectful.
  unfold ProbMonad.equiv in *.
  sets_unfold.
  intros x y H f g H0.
  unfold ProbMonad.imply_event.
  simpl.
  unfold ProbMonad.__bind.
  sets_unfold.
  pose proof x.(legal).(Legal_exists) as [dA_x Hdx].
  pose proof y.(legal).(Legal_exists) as [dA_y Hdy].
  pose proof x.(legal).(Legal_legal) dA_x Hdx as H_legal_x.
  pose proof y.(legal).(Legal_legal) dA_y Hdy as H_legal_y.
  assert (exists a, In a dA_x.(pset)) as Ha. {
    pose proof ProbDistr.legal_prob_1 dA_x H_legal_x as H_prob_1.
    destruct dA_x.(pset) as [|a l].
    - exfalso.
      unfold sum_prob in H_prob_1.
      simpl in H_prob_1.
      lra.
    - exists a.
      left.
      reflexivity.
  }
  destruct Ha as [a H_in_a].
  pose proof H0 a as [dP_a [dP_b [Hda [Hdb H_imp]]]].
  exists dP_a, dP_b.
  repeat split; auto.
  + exists dA_x.
    (* 构造list_r，把dP_a.(pset)的每个元素a_i映射成其概率dA_x.(prob) a_i *)
    set (list_r := map dA_x.(prob) dA_x.(pset)).
    (* 构造list_d，均为dP_a，长度为dA_x.(pset)的长度 *)
    set (list_d := repeat dP_a (length dA_x.(pset))).
    (* 证明list_r和list_d的长度相等 *)
    assert (length list_r = length list_d) as H_length_rd. {
      unfold list_r, list_d.
      rewrite map_length, repeat_length.
      reflexivity.
    }
    set (l := combine list_r list_d).
    assert (length l = length dA_x.(pset)) as H_length_l. {
      unfold l.
      (* Search (length (combine _ _)). *)
      pose proof combine_length list_r list_d as H_combine_length.
      (* Search (Init.Nat.min). *)
      assert (Init.Nat.min (length list_r) (length list_d) = length list_r). {
        rewrite H_length_rd.
        apply Nat.min_id.
      }
      rewrite H_combine_length, H1.
      unfold list_r.
      rewrite map_length.
      reflexivity.
    }
    exists l.
    repeat split; auto.
    - pose proof forall_to_forall2 dA_x.(pset) l (fun (a0 : A) '(r, d) => r = dA_x.(prob) a0 /\ (f a0).(distr) d) as H_forall2.
      apply H_forall2.
      intros a0 [r d] H_in_combine.
      * Search (combine).
        Search (nth_error).
        pose proof In_nth _ _ (a0, (r, d)) H_in_combine as [n Hnth].
        destruct Hnth as [Hn Hnth].
        Search (nth _ (combine _ _)).
        apply symmetry in H_length_l.
        pose proof combine_nth dA_x.(pset) l n a0 (r, d) H_length_l as H_nth_ard.
        rewrite Hnth in H_nth_ard.
        injection H_nth_ard as H_nth_a H_nth_l.
        unfold l in H_nth_l.
        pose proof combine_nth list_r list_d n r d H_length_rd as H_nth_rd.
        rewrite H_nth_rd in H_nth_l.
        injection H_nth_l as H_nth_r H_nth_d.
        split.
        -- Search (nth _ (map _ _) _).
           pose proof map_nth dA_x.(prob) dA_x.(pset) a0 n as H_map.
           rewrite <- H_nth_a in H_map.
           unfold list_r in H_nth_r.
           Search (nth).
           pose proof nth_indep (map dA_x.(prob) dA_x.(pset)) as H_nth_indep.
           specialize (H_nth_indep n r (dA_x.(prob) a0)).
           assert (n < length (map dA_x.(prob) dA_x.(pset))) as Hn_lt. {
             rewrite map_length.
             assert (length (combine dA_x.(pset) l) = length dA_x.(pset)). {
               pose proof combine_length dA_x.(pset) l as H_combine_length.
               rewrite H_length_l in H_combine_length.
               assert (Init.Nat.min (length l) (length l) = length l) by apply Nat.min_id.
               rewrite H1 in H_combine_length.
               rewrite H_length_l.
               assumption.
             }
             rewrite <- H1.
              assumption.
           }
           pose proof H_nth_indep Hn_lt.
           rewrite H_nth_r, <- H_map.
           assumption.
        -- unfold list_d in H_nth_d.
           Search (In _ (combine _ _)).
           pose proof in_combine_r dA_x.(pset) l a0 (r, d) H_in_combine.
           unfold l in H1.
           pose proof in_combine_r list_r list_d r d H1.
           unfold list_d in H2.
           Search (repeat).
           pose proof repeat_spec (length dA_x.(pset)) dP_a d H2.
           rewrite H3.
           pose proof H0 a0.
           destruct H4 as [dP_a0 [dP_b0 [Hda0 [Hdb0 H_imp0]]]].
Admitted. *)
      
Lemma ProbDistr_imply_event_equiv_event:
  forall d1 d2,
    ProbDistr.imply_event d1 d2 ->
    ProbDistr.imply_event d2 d1 ->
    ProbDistr.equiv_event d1 d2.
Proof.
  intros d1 d2 H1 H2.
  unfold ProbDistr.equiv_event.
  unfold ProbDistr.imply_event in *.
  destruct H1 as [r1 [r2 [H11 [H12 H13]]]].
  destruct H2 as [r1' [r2' [H21 [H22 H23]]]].
  pose proof compute_pr_same d1 r1 r2' H11 H22 as Heq1.
  pose proof compute_pr_same d2 r2 r1' H12 H21 as Heq2.
  subst r1' r2'.
  assert (r1 = r2) as Heq by lra.
  subst r2.
  clear H23 H13 H12 H22.
  exists r1, r1.
  repeat split; auto.
Qed.

#[export] Instance ProbMonad_bind_congr_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv_event ==>
          ProbMonad.equiv_event)
    (@bind _ ProbMonad A Prop).
Proof. (** Level 2 *)
  unfold Proper, pointwise_relation, respectful.
  unfold ProbMonad.equiv, ProbMonad.equiv_event in *.
  sets_unfold.
  intros x y H f g H0.
  pose proof (x <- x;; f x).(legal).(Legal_exists) as [dx Hdx].
  pose proof (x <- y;; g x).(legal).(Legal_exists) as [dy Hdy].
  exists dx, dy.
  repeat split; auto.
  assert (ProbDistr.imply_event dx dy) as H_imp_xy. {
    pose proof ProbMonad_bind_mono_event A x y H f g.
    assert (pointwise_relation A ProbMonad.imply_event f g). {
      unfold pointwise_relation.
      unfold ProbMonad.imply_event.
      intros.
      specialize (H0 a).
      destruct H0 as [d1 [d2 [Hf [Hg Heq]]]].
      exists d1, d2.
      repeat split; auto.
      apply ProbDistr_imply_event_refl_setoid in Heq.
      assumption.
    }
    pose proof H1 H2.
    unfold ProbMonad.imply_event in H3.
    destruct H3 as [d1 [d2 [Hd1 [Hd2 H_imp]]]].
    pose proof (x <- x;; f x).(legal).(Legal_unique) as H_unique_f.
    pose proof H_unique_f dx d1 Hdx Hd1.
    apply ProbDistr_equiv_equiv_event in H3.
    pose proof (x <- y;; g x).(legal).(Legal_unique) as H_unique_g.
    pose proof H_unique_g dy d2 Hdy Hd2.
    apply ProbDistr_equiv_equiv_event in H4.
    apply ProbDistr_imply_event_refl_setoid in H3.
    apply symmetry in H4.
    apply ProbDistr_imply_event_refl_setoid in H4.
    transitivity d1; auto.
    transitivity d2; auto.
  }
  assert (ProbDistr.imply_event dy dx) as H_imp_yx. {
    assert (forall a, y.(distr) a <-> x.(distr) a) as H_sym. {
      intros a.
      split; intros.
      - apply (H a).
        assumption.
      - pose proof H a.
        apply H2.
        assumption.
    }
    pose proof ProbMonad_bind_mono_event A y x H_sym g f.
    assert (pointwise_relation A ProbMonad.imply_event g f). {
      unfold pointwise_relation.
      unfold ProbMonad.imply_event.
      intros.
      specialize (H0 a).
      destruct H0 as [d1 [d2 [Hf [Hg Heq]]]].
      exists d2, d1.
      repeat split; auto.
      apply symmetry in Heq.
      apply ProbDistr_imply_event_refl_setoid in Heq.
      assumption.
    }
    pose proof H1 H2.
    unfold ProbMonad.imply_event in H3.
    destruct H3 as [d1 [d2 [Hd1 [Hd2 H_imp]]]].
    pose proof (x <- x;; f x).(legal).(Legal_unique) as H_unique_f.
    pose proof H_unique_f dx d2 Hdx Hd2.
    apply ProbDistr_equiv_equiv_event in H3.
    pose proof (x <- y;; g x).(legal).(Legal_unique) as H_unique_g.
    pose proof H_unique_g dy d1 Hdy Hd1.
    apply ProbDistr_equiv_equiv_event in H4.
    apply ProbDistr_imply_event_refl_setoid in H4.
    apply symmetry in H3.
    apply ProbDistr_imply_event_refl_setoid in H3.
    transitivity d2; auto.
    transitivity d1; auto.
  }
  pose proof ProbDistr_imply_event_equiv_event.
  auto.
Qed.

Lemma list_eq_nil:
  forall (A : Type) (l : list A),
    (forall x, In x l -> False) ->
    l = [].
Proof.
  intros A l H.
  destruct l as [|x xs].
  - reflexivity.
  - simpl in H. exfalso. specialize (H x).
    apply H. left. reflexivity.
Qed.

Lemma one_element_list:
  forall {A: Type} {l: list A} {a},
    In a l -> (forall b, b <> a -> ~ In b l) -> NoDup l -> l = [a].
Proof.
  intros A l a H_in H_unique H_nodup.
  induction l as [|x xs IH].
  - (* l = [] *)
    simpl in H_in.
    contradiction.
  - (* l = x :: xs *)
    simpl in H_in.
    destruct H_in as [H_eq | H_in'].
    + (* x = a *)
      (* 需要证明 xs = [] *)
      assert (forall y, In y xs -> y = a).
      {
        intros y H_y.
        specialize (H_unique y).
        destruct (classic (y = a)) as [Hya | Hnya].
        * assumption.
        * exfalso.
          apply H_unique.
          -- exact Hnya.
          -- right. exact H_y.
      }
      (* 由于 l 没有重复元素，且所有 y ∈ xs 都等于 a，因此 xs 必须为空 *)
      assert (xs = []).
      {
        apply list_eq_nil.
        intros y H_y.
        specialize (H y).
        assert (y = a) by auto.
        subst.
        apply NoDup_cons_iff in H_nodup.
        destruct H_nodup as [H_nodup _].
        tauto.
      }
      subst.
      reflexivity.
    + (* In a xs *)
      (* 由于 H_unique 表明除了 a 之外，列表中没有其他元素，且 x ∈ l *)
      (* 因此 x 必须等于 a *)
      assert (x = a).
      {
        specialize (H_unique x).
        destruct (classic (x = a)) as [Hxa | Hxna].
        * exact Hxa.
        * exfalso.
          apply H_unique.
          -- exact Hxna.
          -- left. reflexivity.
      }
      subst x.
      (* 现在 l = a :: xs，且 NoDup l *)
      (* 根据 H_unique，xs 中不能有元素不同于 a，但 l 无重复元素，故 xs 必须为空 *)
      assert (xs = []).
      {
        apply list_eq_nil.
        intros y H_y.
        specialize (H_unique y).
        destruct (classic (y = a)) as [Hya | Hnya].
        * subst.
          apply NoDup_cons_iff in H_nodup.
          destruct H_nodup as [H_nodup _].
          tauto.
        * exfalso. apply H_unique.
          -- exact Hnya.
          -- right. exact H_y.          
      }
      rewrite H.
      reflexivity.
Qed.

#[export] Instance ProbMonad_ret_mono_event:
  Proper (Basics.impl ==> ProbMonad.imply_event) ret.
Proof. (** Level 2 *)
  unfold Proper, Basics.impl, ProbMonad.imply_event.
  intros P Q H.
  simpl.
  unfold ProbMonad.__ret.
  unfold ProbDistr.is_det.
  sets_unfold.
  (* set d1 as Distr with d1.(pset) = [P] and d1.(prob) = 1%R*)
  set (d1_prob := fun X => if eq_dec X P then 1%R else 0%R).
  set (d1_pset := [P]).
  set (d1:= {|
    ProbDistr.pset := d1_pset;
    ProbDistr.prob := d1_prob
  |}).
  (* set d2 as Distr with d2.(pset) = [Q] and d2.(prob) = 1%R*)
  set (d2_prob := fun X => if eq_dec X Q then 1%R else 0%R).
  set (d2_pset := [Q]).
  set (d2:= {|
    ProbDistr.pset := d2_pset;
    ProbDistr.prob := d2_prob
  |}).
  exists d1, d2.
  assert (d1_prob P = 1%R) as Hp. {
    unfold d1_prob.
    destruct (eq_dec P P).
    - reflexivity.
    - contradiction.
  }
  assert (d2_prob Q = 1%R) as Hq. {
    unfold d2_prob.
    destruct (eq_dec Q Q).
    - reflexivity.
    - contradiction.
  }
  repeat split; auto.
  + assert (forall X, P <> X -> d1_prob X = 0%R). {
      unfold d1_prob.
      intros.
      destruct (eq_dec X P).
      + symmetry in e.
        contradiction.
      + reflexivity.
    }
    intros.
    pose proof H0 b.
    tauto.
  + assert (forall X, Q <> X -> d2_prob X = 0%R). {
      unfold d2_prob.
      intros.
      destruct (eq_dec X Q).
      + symmetry in e.
        contradiction.
      + reflexivity.
    }
    intros.
    pose proof H0 b.
    tauto.
  + unfold ProbDistr.imply_event.
    pose proof ProbDistr_compute_pr_exists as Hex.
    pose proof Hex d1 as [r1 H1].
    pose proof Hex d2 as [r2 h2].
    exists r1, r2.
    repeat split; auto.
    clear Hex.
    unfold ProbDistr.compute_pr in *.
    destruct H1 as [l1 [H11 [H12 H13]]].
    destruct h2 as [l2 [H21 [H22 H23]]].
    simpl in *.
    destruct (classic P).
    - assert (In P l1) as H_in_p. {
        specialize (H11 P).
        tauto.
      }
      assert (forall X, X <> P -> ~ In X l1) as H_unique_p. {
        intros X H_neq.
        unfold not in *.
        intros H_in_x.
        specialize (H11 X).
        assert (P = X) as H_eq_px by tauto.
        apply symmetry in H_eq_px.
        pose proof H_neq H_eq_px.
        contradiction.
      }
      assert (l1 = [P]). {
        pose proof one_element_list H_in_p H_unique_p H13.
        assumption.
      }
      assert (In Q l2) as H_in_q. {
        specialize (H21 Q).
        tauto.
      }
      assert (forall X, X <> Q -> ~ In X l2) as H_unique_q. {
        intros X H_neq.
        unfold not in *.
        intros H_in_x.
        specialize (H21 X).
        assert (Q = X) as H_eq_qx by tauto.
        apply symmetry in H_eq_qx.
        pose proof H_neq H_eq_qx.
        contradiction.
      }
      assert (l2 = [Q]). {
        pose proof one_element_list H_in_q H_unique_q H23.
        assumption.
      }
      subst.
      unfold sum_prob.
      simpl.
      lra.
    - assert (l1 = []) as H_l1_nil. {
        apply list_eq_nil.
        intros X H_in_x.
        specialize (H11 X).
        assert (P = X /\ X) by tauto.
        destruct H1.
        subst X.
        contradiction.
      }
      destruct (classic Q).
      * assert (In Q l2) as H_in_q. {
          specialize (H21 Q).
          tauto.
        }
        assert (forall X, X <> Q -> ~ In X l2) as H_unique_q. {
          intros X H_neq.
          unfold not in *.
          intros H_in_x.
          specialize (H21 X).
          assert (Q = X) as H_eq_qx by tauto.
          apply symmetry in H_eq_qx.
          pose proof H_neq H_eq_qx.
          contradiction.
        }
        assert (l2 = [Q]). {
          pose proof one_element_list H_in_q H_unique_q H23.
          assumption.
        }
        subst.
        unfold sum_prob.
        simpl.
        lra.
      * assert (l2 = []) as H_l2_nil. {
          apply list_eq_nil.
          intros X H_in_x.
          specialize (H21 X).
          assert (Q = X /\ X) by tauto.
          destruct H2.
          subst X.
          contradiction.
        }
        subst.
        unfold sum_prob.
        simpl.
        lra.
Qed.

Lemma ProbMonad_imply_event_equiv_event:
  forall f1 f2,
    ProbMonad.imply_event f1 f2 ->
    ProbMonad.imply_event f2 f1 ->
    ProbMonad.equiv_event f1 f2.
Proof.
  intros f1 f2 H1 H2.
  unfold ProbMonad.equiv_event.
  unfold ProbMonad.imply_event in *.
  destruct H1 as [d1 [d2 [H11 [H12 H13]]]].
  destruct H2 as [d1' [d2' [H21 [H22 H23]]]].
  pose proof f1.(legal).(Legal_unique) as H_unique_f1.
  specialize (H_unique_f1 d1 d2' H11 H22).
  apply ProbDistr_equiv_equiv_event in H_unique_f1.
  pose proof f2.(legal).(Legal_unique) as H_unique_f2.
  specialize (H_unique_f2 d2 d1' H12 H21).
  apply ProbDistr_equiv_equiv_event in H_unique_f2.
  exists d1, d2.
  repeat split; auto.
  pose proof ProbDistr_imply_event_refl_setoid d2 d1' H_unique_f2 as H_imp1.
  apply symmetry in H_unique_f1.
  pose proof ProbDistr_imply_event_refl_setoid d2' d1 H_unique_f1 as H_imp2.
  assert (ProbDistr.imply_event d2 d1). {
    transitivity d2'; auto.
    transitivity d1'; auto.
  }
  pose proof ProbDistr_imply_event_equiv_event d1 d2 H13 H.
  assumption.
Qed.

#[export] Instance ProbMonad_ret_congr_event:
  Proper (iff ==> ProbMonad.equiv_event) ret.
Proof. (** Level 2 *)
  unfold Proper, respectful.
  intros P Q H.
  destruct H as [Hpq Hqp].
  pose proof ProbMonad_ret_mono_event as Hmono.
  unfold Proper, Basics.impl in Hmono.
  pose proof Hmono P Q Hpq.
  pose proof Hmono Q P Hqp.
  apply ProbMonad_imply_event_equiv_event; auto.
Qed.

Lemma Forall2_imply:
  forall {A B: Type} (l1: list A) (l2: list B) (P Q: A -> B -> Prop) ,
    Forall2 P l1 l2 ->
    (forall a b, 
      In a l1 -> In b l2 -> P a b -> Q a b) ->
    Forall2 Q l1 l2.
Proof.
  intros A B l1 l2  P Q H_forall2 H_imp.
  induction H_forall2.
  - constructor.
  - constructor.
    + apply H_imp.
      all: simpl; auto.
    + apply IHH_forall2.
      intros.
      apply H_imp.
      all: simpl; auto.
Qed.


Lemma map_map_eq_Forall2:
  forall {A B C: Type} (l1: list A) (l2: list B) (f: A -> C) (g: B -> C),
    Forall2 (fun a b => f a = g b) l1 l2 ->
    map f l1 = map g l2.
Proof.
  intros A B C l1 l2 f g H_forall2.
  induction H_forall2.
  - reflexivity.
  - simpl.
    rewrite IHH_forall2.
    rewrite H.
    reflexivity.
Qed.

Lemma In_combine_Forall2:
  forall {A B: Type} (l1: list A) (l2: list B) (a: A) (b: B) (f: A -> B -> Prop),
    In (a, b) (combine l1 l2) ->
    Forall2 f l1 l2 ->
    f a b.
Proof.
Admitted.

Lemma combine_exists:
  forall {A B: Type} (l: list (A * B)),
  exists l1 l2,
    l = combine l1 l2.
Proof.
  intros A B l.
  induction l as [| [a b] l IH].
  - exists [], [].
    reflexivity.
  - destruct IH as [l1 [l2 IH]].
    exists (a :: l1), (b :: l2).
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma combine_permutation_l_exists_holds:
  forall {A B: Type} (l1: list A) (l2: list B)
    (l1': list A),
    Permutation l1 l1' ->
    exists l2',
      Permutation l2 l2' /\
      Permutation (combine l1 l2) (combine l1' l2') /\
      (* all the Forall2 still holds *)
      (forall pred, Forall2 pred l1 l2 -> Forall2 pred l1' l2').
Proof.
Admitted.

Lemma combine_Forall2:
  forall {A B C: Type} (l1: list A) (l2: list B) (l3: list C) (f: A -> B -> C -> Prop),
    (forall a b c,
      In (a, b) (combine l1 l2) ->
      In (a, c) (combine l1 l3) ->
      f a b c ) ->
    Forall2 (fun '(a, b) '(a', c) => a=a' /\ f a b c) (combine l1 l2) (combine l1 l3).
Proof.
Admitted.
      

Lemma Permutation_filter_dup_concat_incl:
  forall {A: Type} (l1: list A) (l2: list (list A)),
    Permutation l1 (filter_dup (concat l2)) ->
    (
      forall l, In l l2 -> incl l l1
    ).
Proof.
Admitted.


Lemma bind_assoc:
  forall (A B C: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).
Proof.
  intros.
  unfold ProbMonad.equiv.
  sets_unfold.
  intros dc.
  simpl.
  split.
  {
    unfold ProbMonad.__bind.
    intros H.
    destruct H as [db [lbc H]].
    destruct H as [Hdb [Hlbc H_sum_distr_lbdc]].
    destruct Hdb as [da [lab [Hda [Hlab H_sum_distr_ladb]]]].

    assert (
      exists lac: list (R * Distr C),
        Forall2 (fun a '(r, d) => 
                  r = da.(prob) a /\ 
                  exists ga: Distr B, (g a).(distr) ga /\
                  exists l_sum_to_bc: list (R * Distr C),
                    (Forall2 (fun b '(r, d) => 
                                r = ga.(prob) b /\ d ∈ (h b).(distr)) 
                      ga.(pset) l_sum_to_bc) /\
                      ProbDistr.sum_distr l_sum_to_bc d)
        da.(pset) lac
    ) as H_exists_lac. 
    {
      clear Hlab.
      induction da.(pset) as [|a l].
      - exists nil.
        repeat constructor.
      - destruct IHl as [lac Hlac].
        pose proof (g a).(legal).(Legal_exists) as [ga Hga].
        pose proof (bind (g a) h).(legal).(Legal_exists) as [ga_h Hga_h].
        exists ((da.(prob) a, ga_h) :: lac).
        constructor.
        2: {
          apply Hlac.
        }
        sets_unfold in Hga.
        sets_unfold in Hga_h.
        split; auto.
        simpl in Hga_h.
        unfold ProbMonad.__bind in Hga_h.
        sets_unfold in Hga_h.
        destruct Hga_h as [gb [lbc' [Hgb [Hlbc' H_sum_gb]]]].
        pose proof (g a).(legal).(Legal_unique) _ _ Hga Hgb as H_unique_ga_gb.
        destruct H_unique_ga_gb as [H_prob_ga_gb H_perm_ga_gb].
        assert (ga.(prob) = gb.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
        symmetry in H_perm_ga_gb.
        pose proof Forall2_perm_l_exists _ _ _ _ H_perm_ga_gb Hlbc' as [lbc'' [Hlbc''_1 Hlbc''_2]].
        exists ga.
        split; auto.
        exists lbc''.
        split; auto.
        + rewrite H_prob_eq.
          apply Hlbc''_2.
        + rewrite <- Hlbc''_1.
          apply H_sum_gb.
    }
    destruct H_exists_lac as [lac Hlac].
    exists da, lac.
    split.
    2: split.
    {
      auto.
    }
    {
      pose proof Forall2_imply da.(pset) lac as H_forall2_imply.
      eapply H_forall2_imply. 1: apply Hlac.
      clear H_forall2_imply.
      (* prove the above predicate imply the below one *)
      intros a [r d].
      intros H_in_da H_in_lac [H_eq H_exists].
      destruct H_exists as [ga [Hga [l_sum_to_bc [H_forall2_bc H_sum_bc]]]].
      split; auto.
      sets_unfold.
      exists ga, l_sum_to_bc.
      split; auto.
    }
    split.
    {
      destruct H_sum_distr_lbdc as [H_sum_lbdc _].
      destruct H_sum_distr_ladb as [H_sum_ladb _].
      rewrite H_sum_lbdc.
      apply Permutation_filter_dup_filter_dup_incl_inv.
      intros c.
      split.
      {
        intros H_c_in_lbc.
        pose proof In_concat_map_exists _ _ _ H_c_in_lbc as H_c_in_lbc_ex.
        destruct H_c_in_lbc_ex as [[r dc'] [H_in_lbc' H_in_dc']].
        pose proof Forall2_in_r_exists _ _ _ Hlbc _ H_in_lbc' as H_lbc'.
        destruct H_lbc' as [b [H_in_dbpset [_ H_dc'_hb]]].
        rewrite H_sum_ladb in H_in_dbpset.
        apply filter_dup_incl in H_in_dbpset.
        pose proof In_concat_map_exists _ _ _ H_in_dbpset as H_in_dbpset_ex.
        destruct H_in_dbpset_ex as [[r' db'] [H_in_lab' H_in_db']].
        pose proof Forall2_in_r_exists _ _ _ Hlab _ H_in_lab' as H_lab'.
        destruct H_lab' as [a' [H_in_dapset [_ H_dc'_ha]]].

        pose proof Forall2_in_l_exists _ _ _ Hlac _ H_in_dapset as H_lac.
        destruct H_lac as [[rb dc''] [H_in_lac' [_ H2]]].
        destruct H2 as [gb [H_gb [l_sum_to_bc [H_forall2_bc H_sum_bc]]]].

        apply In_in_concat_map.
        exists (rb, dc''); split; auto.

        destruct H_sum_bc as [H_sum_bc _].
        rewrite H_sum_bc.
        apply filter_dup_in_inv.
        apply In_in_concat_map.

        assert (Permutation db'.(pset) gb.(pset)) as H_perm_db'pset_gbpset. {
          pose proof (g a').(legal).(Legal_unique) _ _ H_dc'_ha H_gb as H_unique_ga_gb.
          destruct H_unique_ga_gb as [_ H_perm_eq].
          assumption.
        }
        symmetry in H_perm_db'pset_gbpset.
        pose proof Forall2_perm_l_exists _ _ _ _ H_perm_db'pset_gbpset H_forall2_bc as [l_sum_to_bc' [H_perm_bc_bc' H_forall2_bc']].

        pose proof Forall2_in_l_exists _ _ _ H_forall2_bc' _ H_in_db' as H_bc.
        destruct H_bc as [[rc dc'''] [H_in_gbpset [H_prob_eq H_in_hb]]].
        exists (rc, dc''').
        split; [rewrite H_perm_bc_bc'; auto|].

        (* dc' anc dc''' are both from (h b).(distr) *)
        pose proof (h b).(legal).(Legal_unique) _ _ H_in_hb H_dc'_hb as H_unique_dc'_dc'''.
        destruct H_unique_dc'_dc''' as [_ H_perm_dc'_dc'''].
        rewrite H_perm_dc'_dc'''.
        assumption.
      }
      {
        admit. (* should be similar *)
      }
    }
    {
      intros c.
      destruct H_sum_distr_ladb as [_ H_sum_ladb].
      destruct H_sum_distr_lbdc as [_ H_sum_lbdc].
      rewrite H_sum_lbdc.
      remember (sum (map (fun '(r, d) => (r * d.(prob) c)%R) lbc)) as lhs.
      assert (
        lhs
        =
        sum (map (fun '(b, (r, d)) => (db.(prob) b * d.(prob) c)%R) (combine db.(pset) lbc))
      ) as Hlhs1.
      {
        subst lhs.
        f_equal.
        clear H_sum_lbdc.
        induction Hlbc.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlbc.
          destruct y.
          destruct H.
          rewrite H.
          reflexivity.
      }
      clear Heqlhs.
      assert (
        db.(prob)
        =
        fun b => sum (map (fun '(r, d) => (r * d.(prob) b)%R) lab)
      ) as Hdbprob by (apply functional_extensionality; auto).
      assert (
        (fun b : B => sum (map (fun '(r, d) => (r * d.(prob) b)%R) lab))
        =
        fun b => sum (map (fun '(a, (r, d)) => (da.(prob) a * d.(prob) b)%R) (combine da.(pset) lab))
      ). {
        apply functional_extensionality.
        intros b.
        f_equal.
        clear H_sum_ladb.
        clear Hlac.
        clear Hdbprob.
        induction Hlab.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlab.
          destruct y.
          destruct H.
          rewrite H.
          reflexivity.
      }
      rewrite H in Hdbprob.
      clear H.
      rewrite Hdbprob in Hlhs1.
      clear Hdbprob.

      (* Check sum_map_sum_map. *)

      assert (
        lhs =
        sum
          (map
             (fun '(b, y) =>
              let
              '(_, d) := y in
               (sum
                  (map
                     (fun '(a, y0) =>
                      let
                      '(_, d0) := y0 in
                       da.(prob) a * d0.(prob) b * 
                       d.(prob) c)
                     (combine da.(pset) lab)) )%R) (combine db.(pset) lbc))
      ) as Hlhs2. {
        subst lhs.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [b [r d]].
        pose proof sum_map_multi (combine da.(pset) lab) (fun '(a, y) =>
        let '(_, d0) := y in da.(prob) a * d0.(prob) b)%R (d.(prob) c).
        (* SearchRewrite (_ * _)%R. *)
        rewrite Rmult_comm.
        rewrite <- H.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [a [r' d0]].
        lra.
      }
      clear Hlhs1.
      pose proof sum_map_sum_map as H.
      specialize (H _ _ (combine db.(pset) lbc) (combine da.(pset) lab)).
      specialize (H 
      (
          (fun '(a, y0) =>
          let
          '(_, d0) := y0 in
          fun '(b, y) =>
          let
          '(_, d) := y in
          ((da.(prob) a) * (d0.(prob) b) * (d.(prob) c))%R))
      ).
      assert (lhs =
      sum
      (map
         (fun a : B * (R * Distr C) =>
          sum
            (map
               (fun b : A * (R * Distr B) =>
                (fun '(a0, y0) =>
                 let
                 '(_, d0) := y0 in
                  fun '(b0, y) =>
                  let
                  '(_, d) := y in
                   (da.(prob) a0 * d0.(prob) b0 * d.(prob) c)%R) b a)
               (combine da.(pset) lab))) (combine db.(pset) lbc))
      ) as H_lhs3. {
        clear H.
        subst lhs.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [b [r d]].
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [a [r' d0]].
        lra.
      }
      clear Hlhs2.
      remember (sum
      (map
         (fun a : B * (R * Distr C) =>
          sum
            (map
               (fun b : A * (R * Distr B) =>
                (fun '(a0, y0) =>
                 let
                 '(_, d0) := y0 in
                  fun '(b0, y) =>
                  let
                  '(_, d) := y in
                   (da.(prob) a0 * d0.(prob) b0 * d.(prob) c)%R) b a)
               (combine da.(pset) lab))) (combine db.(pset) lbc))) as lhs4.
      rewrite H in H_lhs3.
      clear H lhs4 Heqlhs4.

      (* clear H_lhs3. *)
      remember (sum (map (fun '(r, d) => (r * d.(prob) c)%R) lac)) as rhs.
      assert (
        (* sum (map (fun '(r, d) => (r * d.(prob) c)%R) lac) *)
        rhs = 
        sum (map (fun '(a, (r, d)) => (da.(prob) a * d.(prob) c)%R) (combine da.(pset) lac))
      ) as Hrhs1. {
        clear H_lhs3.
        subst rhs.
        f_equal.
        clear H_sum_lbdc.
        clear Hlab.
        induction Hlac.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlac.
          destruct y.
          destruct H.
          rewrite H.
          reflexivity.
      }
      clear Heqrhs.

      subst rhs.
      subst lhs.
      f_equal.
      (* Search (map _ _ = map _ _). *)
      apply map_map_eq_Forall2.

      remember (fun (a : A * (R * Distr B)) (b : A * (R * Distr C))
      =>
      sum
        (map
           (fun a0 : B * (R * Distr C) =>
            (let
             '(a1, y0) := a in
              let
              '(_, d0) := y0 in
               fun '(b0, y) =>
               let
               '(_, d) := y in
                (da.(prob) a1 * d0.(prob) b0 * d.(prob) c)%R)
              a0) (combine db.(pset) lbc)) =
      (let
       '(a0, y) := b in
        let '(_, d) := y in (da.(prob) a0 * d.(prob) c)%R))
      as pred.
      enough (
        forall a b c,
        In (a, b) (combine da.(pset) lab) ->
        In (a, c) (combine da.(pset) lac) ->
        pred (a, b) (a, c)
      ). {
        pose proof combine_Forall2 da.(pset) lab lac.
        specialize (H0 (fun a b c => pred (a, b) (a, c))).
        specialize (H0 H).
        eapply Forall2_imply.
        - apply H0.
        - intros.
          destruct a, b.
          destruct H3.
          subst a.
          assumption.
      }
      subst pred.
      intros a [r1 d1] [r2 d2] H_in_lab H_in_lac.
      (* Search combine. *)
      pose proof In_combine_Forall2 _ _ _ _ _ H_in_lab Hlab as Har1d1.
      pose proof In_combine_Forall2 _ _ _ _ _ H_in_lac Hlac as Har2d2.
      simpl in Har1d1, Har2d2.
      destruct Har1d1 as [H_r1 H_d1].
      destruct Har2d2 as [H_r2 H_d2].
      destruct H_d2 as [ga [Hga [l_sum_to_bc [H_forall2_bc H_sum_bc]]]].
      destruct H_sum_bc as [_ H_sum_bc].
      assert (
        sum
          (map
            (fun '(b0, y) =>
              let
              '(_, d) := y in
              (da.(prob) a * d1.(prob) b0 * d.(prob) c)%R)
            (combine db.(pset) lbc))
     =
     da.(prob) a * 
        sum
          (map
              (fun '(b0, y) =>
              let
              '(_, d) := y in
                (d1.(prob) b0 * d.(prob) c)%R)
              (combine db.(pset) lbc))
      )%R. {
        rewrite <- sum_map_multi.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [b0 [r d]].
        lra.
      }
      rewrite H; clear H.
      apply Rmult_eq_compat_l.
      rewrite H_sum_bc.

      (* rhs *)
      assert (
        sum 
        (map 
          (fun '(r, d) => (r * d.(prob) c)%R) 
          l_sum_to_bc
        )
        =
        sum 
        (map 
          (fun '(b0, (r, d)) => (ga.(prob) b0 * d.(prob) c)%R) (combine ga.(pset) l_sum_to_bc))
        ) as H_rhs1. {
          f_equal.
          clear H_sum_bc.
          induction H_forall2_bc.
          - simpl. reflexivity.
          - simpl.
            rewrite IHH_forall2_bc.
            destruct y.
            destruct H.
            rewrite H.
            reflexivity.
        }
        rewrite H_rhs1; clear H_rhs1.
        pose proof (g a).(legal).(Legal_unique) _ _ Hga H_d1 as H_unique_ga_d1.
        destruct H_unique_ga_d1 as [H_prob_ga_d1 H_perm_ga_d1].

        (* summing db.(pset) with d1.(prob)
           is equal to summing along the d1.(pset)
           as all those b's not in d1.(pset) get a multiplier of 0.  *)

        remember (fun '(b0, y) =>
        let '(_, d) := y in (d1.(prob) b0 * d.(prob) c)%R) as calc.
        assert (
          exists filtered_dbpset filtered_lbc,
          sum (map calc (combine filtered_dbpset filtered_lbc)) =
          sum (map calc (combine db.(pset) lbc))
          /\
          filtered_dbpset = d1.(pset)
          /\ (* The order is conserved, so any Forall2 preds on this still holds *)
          (forall pred, Forall2 pred db.(pset) lbc -> Forall2 pred filtered_dbpset filtered_lbc)
        ). {
          (* exists (filter (fun '(b0, _) => if in_dec eq_dec b0 d1.(pset) then true else false) (combine db.(pset) lbc)).
          repeat split.
          - pose proof list_partition_in_notin d1.(pset) (map fst (combine db.(pset) lbc)) as H.
            destruct H as [in_part [notin_part]].
            destruct H as [H_comb_perm [H_in H_notin]]. *)
            admit.
        }
        destruct H as [dbpset' [lbc' [H_sum_eq [H_dbpset_eq H_forall2_eq]]]].
        pose proof H_forall2_eq _ Hlbc as Hlbc'.
        clear H_forall2_eq.
        rewrite <- H_sum_eq.
        clear H_sum_eq.
        subst dbpset'.
        subst calc.
        pose proof combine_permutation_l_exists_holds _ l_sum_to_bc _ H_perm_ga_d1 as H_perm.
        destruct H_perm as [l_sum_to_bc' [H_perm_l_sum_to_bc [H_perm_combine H_forall2_l_sum_to_bc]]].
        specialize (H_forall2_l_sum_to_bc _ H_forall2_bc).

        rewrite H_perm_combine.
        f_equal.
        apply map_map_eq_Forall2.
        
        remember (fun a0 b : B * (R * Distr C) =>
        (let
         '(b0, y) := a0 in
          let '(_, d) := y in (d1.(prob) b0 * d.(prob) c)%R) =
        (let
         '(b0, y) := b in
          let '(_, d) := y in (ga.(prob) b0 * d.(prob) c)%R)) as pred.
        enough (
          forall a b c,
          In (a, b) (combine d1.(pset) lbc') ->
          In (a, c) (combine d1.(pset) l_sum_to_bc') ->
          pred (a, b) (a, c)
        ). {
          pose proof combine_Forall2 d1.(pset) lbc' l_sum_to_bc'.
          specialize (H0 (fun a b c => pred (a, b) (a, c))).
          specialize (H0 H).
          eapply Forall2_imply.
          - apply H0.
          - intros.
            destruct a0, b.
            destruct H3.
            subst b.
            assumption. 
        }
        subst pred.
        intros b [r3 d3] [r4 d4] H_in_lbc' H_in_l_sum_to_bc'.
        pose proof In_combine_Forall2 _ _ _ _ _ H_in_lbc' Hlbc' as Har3d3.
        pose proof In_combine_Forall2 _ _ _ _ _ H_in_l_sum_to_bc' H_forall2_l_sum_to_bc as Har4d4.
        simpl in Har3d3, Har4d4.
        destruct Har3d3 as [H_r3 H_d3].
        destruct Har4d4 as [H_r4 H_d4].
        pose proof (h b).(legal).(Legal_unique) _ _ H_d3 H_d4 as H_unique_d3_d4.
        destruct H_unique_d3_d4 as [H_prob_d3_d4 H_perm_d3_d4].
        rewrite H_prob_d3_d4.
        rewrite H_prob_ga_d1.
        reflexivity.
    }
  }
  {
    unfold ProbMonad.__bind.
    intros H.
    destruct H as [da [lac [Hda [Hlac H_sum_distr_ladc]]]].
    set ( fg := ProbMonad.bind f g).
    pose proof fg.(legal).(Legal_exists) as [db Hdb].
    assert (
      exists lbc: list (R * Distr C),
        Forall2 (fun b '(r, d) => 
                  r = db.(prob) b /\ 
                  (h b).(distr) d)
        db.(pset) lbc
    ). {
      clear Hlac.
      induction db.(pset) as [|b l].
      - exists nil.
        repeat constructor.
      - destruct IHl as [lbc Hlbc].
        pose proof (h b).(legal).(Legal_exists) as [hb Hhb].
        exists ((db.(prob) b, hb) :: lbc).
        constructor.
        2: {
          apply Hlbc.
        }
        sets_unfold in Hhb.
        split; auto.
    }
    destruct H as [lbc Hlbc].
    exists db, lbc.
    repeat split.
    {
      sets_unfold.
      assert (
        exists lab: list (R * Distr B),
          Forall2 (fun a '(r, d) => 
                    r = da.(prob) a /\ 
                    (g a).(distr) d)
          da.(pset) lab
      ). {
        clear Hdb.
        clear Hlac.
        induction da.(pset) as [|a l].
        - exists nil.
          repeat constructor.
        - destruct IHl as [lab Hlab].
          pose proof (g a).(legal).(Legal_exists) as [ga Hga].
          exists ((da.(prob) a, ga) :: lab).
          constructor.
          2: {
            apply Hlab.
          }
          sets_unfold in Hga.
          split; auto.
      }
      destruct H as [lab Hlab].
      exists da, lab.
      split; auto.
      split; auto.
      pose proof fg.(legal) as Hfg_legal.
      unfold ProbMonad.bind in fg.
      unfold ProbMonad.__bind in fg.
      simpl in Hdb.
      sets_unfold in Hdb.
      destruct Hdb as [da' [lab' [Hda' [Hlab' H_sum_distr_lab'db]]]].
      clear lbc Hlbc H_sum_distr_ladc.

      (* da and da' has perm pset *)
      pose proof f.(legal).(Legal_unique) _ _ Hda Hda' as H_unique_da_da'.
      destruct H_unique_da_da' as [H_prob_da_da' H_perm_da_da'].
      assert (da.(prob) = da'.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
      symmetry in H_perm_da_da'.
      pose proof Forall2_perm_l_exists _ _ _ _ H_perm_da_da' Hlab' as [lab'' [H_perm_lab_lab'' H_forall2_lab'']].
      rewrite H_perm_lab_lab'' in H_sum_distr_lab'db.
      clear H_perm_lab_lab''.
      clear Hlab' lab' Hda'.
      rewrite <- H_prob_eq in H_forall2_lab''.

      assert (
        Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2)
        lab lab''
      ) as Hlab_lab''. {
        clear fg Hfg_legal H_prob_da_da' H_perm_da_da' H_prob_eq H_sum_distr_lab'db.
        pose proof Forall2_pair_Forall2 _ (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) _ _ _ Hlab H_forall2_lab''.
        apply H.
        intros.
        destruct b1, b2.
        destruct H3, H4.
        split.
        - subst.
          reflexivity.
        - pose proof (g a).(legal).(Legal_unique) _ _ H5 H6.
          assumption. 
      }
      pose proof sum_distr_congr_2 _ _ _ Hlab_lab'' H_sum_distr_lab'db.
      assumption.
    }
    {
      auto.
    }
    {
      destruct H_sum_distr_ladc as [H_perm_ladc _].
      rewrite H_perm_ladc.
      apply Permutation_filter_dup_filter_dup_incl_inv.
      intros c.
      split.
      {
        intros H_c_in_ladc.
        pose proof In_concat_map_exists _ _ _ H_c_in_ladc as H_c_in_ladc_ex.
        clear H_c_in_ladc.
        destruct H_c_in_ladc_ex as [[r dc1] [H_in_ladc1 H_in_dc1]].

        (* dc1 is a result from binding a da and a (fun a => bind (g a) h) *)
        pose proof Forall2_in_r_exists _ _ _ Hlac _ H_in_ladc1 as H_lac1.
        destruct H_lac1 as [a1 [H_in_dbpset [_ H_dc1_hb]]].

        sets_unfold in H_dc1_hb.
        (* dc1 is from bind (g a1) h *)
        destruct H_dc1_hb as [db1 [lbc1 [Hdb1 [Hlbc1 H_sum_bc1]]]].

        (* c is from dc1, so it must be from some (h b1). *)
        destruct H_sum_bc1 as [H_sum_bc1 _].
        rewrite H_sum_bc1 in H_in_dc1.
        apply filter_dup_incl in H_in_dc1.
        pose proof In_concat_map_exists _ _ _ H_in_dc1 as H_in_dc1_ex.
        destruct H_in_dc1_ex as [[r' dc2] [H_in_lbc2 H_in_dc2]].
        (* dc2 is from h *)
        pose proof Forall2_in_r_exists _ _ _ Hlbc1 _ H_in_lbc2 as H_lbc2.
        destruct H_lbc2 as [b1 [H_in_db1pset [_ H_dc2_hb]]].

        (* db is bind f g *)
        assert (
          ProbMonad.__bind f.(distr) (fun a : A => (g a).(distr)) db
        ) as Hdb_bind. {
          unfold ProbMonad.bind in fg.
          subst fg.
          simpl in Hdb.
          auto.
        }
        unfold ProbMonad.__bind in Hdb_bind.
        destruct Hdb_bind as [da' [lab' [Hda' [Hlab' H_sum_distr_lab'db]]]].

        (* da and da' are both from f and are thus equiv. unite them first *)
        pose proof f.(legal).(Legal_unique) _ _ Hda Hda' as H_unique_da_da'.
        destruct H_unique_da_da' as [H_prob_da_da' H_perm_da_da'].
        assert (da.(prob) = da'.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
        rewrite <- H_prob_eq in Hlab'.
        clear H_prob_da_da'.
        symmetry in H_perm_da_da'.
        pose proof Forall2_perm_l_exists _ _ _ _ H_perm_da_da' Hlab' as [lab'' [H_perm_lab_lab'' Hlab'']].
        clear Hlab'.
        rewrite H_perm_lab_lab'' in H_sum_distr_lab'db.
        clear lab' H_perm_lab_lab''.
        clear H_prob_eq.

        destruct H_sum_distr_lab'db as [H_sum_lab''db _].

        (* as a1 is from da, now that da and da' are equiv, we know some db' is here in lab'' *)
        pose proof Forall2_in_l_exists _ _ _ Hlab'' _ H_in_dbpset as H_lab''.
        destruct H_lab'' as [[rb' db'] [H_in_lab'' [_ H_db']]].

        (* db1 and db' are all from g a1 and are equiv *)
        pose proof (g a1).(legal).(Legal_unique) _ _ H_db' Hdb1 as H_unique_db'_db1.
        destruct H_unique_db'_db1 as [H_prob_db'_db1 H_perm_db'_db1].
        assert (db'.(prob) = db1.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
        symmetry in H_perm_db'_db1.
        pose proof Forall2_perm_l_exists _ _ _ _ H_perm_db'_db1 Hlbc1 as [lbc1' [H_perm_lbc1_lbc1' Hlbc1']].
        rewrite H_perm_db'_db1 in H_in_db1pset.
        clear H_perm_db'_db1.
        rewrite <- H_prob_eq in Hlbc1.
        clear H_prob_eq.

        (* as b1 is from db1, now that db1 and db' are equiv, we know some dc' is here in lbc1' *)
        pose proof Forall2_in_l_exists _ _ _ Hlbc1' _ H_in_db1pset as H_lbc1'.
        destruct H_lbc1' as [[rc dc'] [H_in_lbc1' [_ H_dc']]].

        (* dc' and dc2 are all from h b1 and are equiv *)
        pose proof (h b1).(legal).(Legal_unique) _ _ H_dc' H_dc2_hb as H_unique_dc'_dc2.
        destruct H_unique_dc'_dc2 as [H_prob_dc'_dc2 H_perm_dc'_dc2].
        assert (dc'.(prob) = dc2.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
        clear H_prob_dc'_dc2.

        assert (
          incl db'.(pset) db.(pset)
        ) as H_db'_incl_db. {
          pose proof Permutation_filter_dup_concat_incl _ _ H_sum_lab''db.
          apply H.
          (* Search map. *)
          pose proof in_map (fun '(_, d) => d.(pset)) lab'' (rb', db') H_in_lab''.
          simpl in H0.
          exact H0.
        }

        apply In_in_concat_map.
        
        (* b1 ∈ db'.(pset) and db'.(pset) ⊆ db.(pset). so b1 has something to do with lbc *)
        assert (In b1 db.(pset)) as H_b1_in_db. {
          apply H_db'_incl_db.
          assumption.
        }
        pose proof Forall2_in_l_exists _ _ _ Hlbc _ H_b1_in_db as H_b1_lbc.
        destruct H_b1_lbc as [[r_b1 dc_b1] [H_in_lbc [_ H_dc_b1]]].
        exists (r_b1, dc_b1).
        split.
        - exact H_in_lbc.
        - (* as dc_b1 comes from b1 and h, it is equiv with dc2.*)
          pose proof (h b1).(legal).(Legal_unique) _ _ H_dc_b1 H_dc2_hb as H_unique_dc_b1_dc2.
          destruct H_unique_dc_b1_dc2 as [H_prob_dc_b1_dc2 H_perm_dc_b1_dc2].
          assert (In c dc2.(pset)) as H by assumption.
          eapply Permutation_in.
          1: symmetry;  apply H_perm_dc_b1_dc2.
          auto.
      }
      {
        (* should be similar *)
        admit.
      }
    }
    {
      intros c.
      destruct H_sum_distr_ladc as [_ H_sum_ladc].
      rewrite (H_sum_ladc c).
      remember (sum (map (fun '(r, d) => (r * d.(prob) c)%R) lac)) as lhs.
      remember (sum (map (fun '(r, d) => (r * d.(prob) c)%R) lbc)) as rhs.
      assert (
        lhs
        =
        sum (map (fun '(a, (r, d)) => (da.(prob) a * d.(prob) c)%R) (combine da.(pset) lac))
      ) as Hlhs1. {
        subst lhs.
        f_equal.
        clear H_sum_ladc.
        induction Hlac.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlac.
          destruct y.
          destruct H.
          rewrite H.
          reflexivity.
      }
      assert (
        rhs
        =
        sum (map (fun '(b, (r, d)) => (db.(prob) b * d.(prob) c)%R) (combine db.(pset) lbc))
      ) as Hrhs1. {
        subst rhs.
        f_equal.
        clear H_sum_ladc.
        induction Hlbc.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlbc.
          destruct y.
          destruct H.
          rewrite H.
          reflexivity.
      }
      clear Heqlhs Heqrhs.

      (* db is from bind f g. Its prob func is known *)
      assert (
        exists (s1 : Distr A) (l : list (R * Distr B)),
        f.(distr) s1 /\
        Forall2 (fun (a : A) '(r, d) => r = s1.(prob) a /\ (g a).(distr) d)
          s1.(pset) l /\ ProbDistr.sum_distr l db
      ) as Hdb_bind. {
        unfold ProbMonad.bind in fg.
        unfold ProbMonad.__bind in fg.
        simpl in Hdb.
        sets_unfold in Hdb.
        assumption.
      }
      destruct Hdb_bind as [da_fg [lab [Hs1 [Hlab H_sum_lab_db]]]].
      clear Hdb.
      destruct H_sum_lab_db as [_ H_prob_db].
      assert (db.(prob) = fun b => sum (map (fun '(r, d) => (r * d.(prob) b)%R) lab)) 
        as H_prob_db_eq
        by (apply functional_extensionality; auto).
      clear H_prob_db.
      rewrite H_prob_db_eq in Hrhs1; clear H_prob_db_eq.
      
      assert (
        rhs =
        sum
          (map
             (fun '(b, y) =>
              let
              '(_, d) := y in
               (sum (map (fun '(a, (r, d0)) => da_fg.(prob) a * d0.(prob) b) (combine da_fg.(pset) lab)
               ) 
               * d.(prob) c)%R)
             (combine db.(pset) lbc))
      ) as Hrhs2. {
        subst rhs.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [b [r d]].
        f_equal.
        f_equal.
        induction Hlab.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlab.
          destruct y.
          destruct H.
          rewrite H.
          reflexivity.
      }
      clear Hrhs1.
      assert (
        rhs = 
        sum
          (map
             (fun '(b, y) =>
              let
              '(_, d) := y in
               (sum
                  (map
                     (fun '(a, y0) =>
                      let '(_, d0) := y0 in da_fg.(prob) a * d0.(prob) b  * 
                      d.(prob) c)
                     (combine da_fg.(pset) lab)))%R) (combine db.(pset) lbc))
      ) as Hrhs3. {
        subst rhs.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [b [r d]].
        rewrite Rmult_comm.
        rewrite <- sum_map_multi.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [a [r' d0]].
        lra.
      }
      clear Hrhs2.
      pose proof sum_map_sum_map as H.
      specialize (H _ _ (combine db.(pset) lbc) (combine da_fg.(pset) lab)).
      specialize (H 
      (
          (fun '(a, y0) =>
          let
          '(_, d0) := y0 in
          fun '(b, y) =>
          let
          '(_, d) := y in
          ((da_fg.(prob) a) * (d0.(prob) b) * (d.(prob) c))%R))
      ).
      assert (rhs =
      sum
      (map
         (fun b : A * (R * Distr B) =>
          sum
            (map
               (fun a : B * (R * Distr C) =>
                (fun '(a0, y0) =>
                 let
                 '(_, d0) := y0 in
                  fun '(b0, y) =>
                  let
                  '(_, d) := y in
                   (da_fg.(prob) a0 * d0.(prob) b0 * d.(prob) c)%R) b a)
               (combine db.(pset) lbc))) (combine da_fg.(pset) lab))
      ) as H_rhs4. {
        rewrite <- H.
        clear H.
        subst rhs.
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [b [r d]].
        f_equal.
        f_equal.
        apply functional_extensionality.
        intros [a [r' d0]].
        reflexivity.
      }
      clear H.
      clear Hrhs3.

      (* da and da_fg are both from f, so they are equiv and pset are perm.*)
      pose proof f.(legal).(Legal_unique) _ _ Hda Hs1 as H_unique_da_da_fg.
      destruct H_unique_da_da_fg as [H_prob_da_da_fg H_perm_da_da_fg].
      assert (da.(prob) = da_fg.(prob)) as H_prob_eq by (apply functional_extensionality; auto).

      (* Search combine. *)
      symmetry in H_perm_da_da_fg.
      pose proof combine_permutation_l_exists_holds _ lab _ H_perm_da_da_fg as H_perm.
      destruct H_perm as [lab' [H_perm_lab_lab' [H_perm_comb_comb' H_forall2_comb_comb']]].
      rewrite H_perm_comb_comb' in H_rhs4.
      pose proof H_forall2_comb_comb' _ Hlab as Hlab'.
      clear Hlab.
      clear H_perm_comb_comb'.
      clear lab H_perm_lab_lab' H_forall2_comb_comb'.


      subst lhs.
      subst rhs.
      f_equal.
      apply map_map_eq_Forall2.

      remember (fun (a : A * (R * Distr C)) (b : A * (R * Distr B)) =>
      (let '(a0, y) := a in let '(_, d) := y in (da.(prob) a0 * d.(prob) c)%R) =
      sum
        (map
           (fun a0 : B * (R * Distr C) =>
            (let
             '(a1, y0) := b in
              let
              '(_, d0) := y0 in
               fun '(b0, y) =>
               let
               '(_, d) := y in (da_fg.(prob) a1 * d0.(prob) b0 * d.(prob) c)%R)
              a0) (combine db.(pset) lbc))) as pred.
      enough (
        forall a b c,
        In (a, b) (combine da.(pset) lac) ->
        In (a, c) (combine da.(pset) lab') ->
        pred (a, b) (a, c)
      ). {
        pose proof combine_Forall2 da.(pset) lac lab' as Har1d1.
        specialize (Har1d1 (fun a b c => pred (a, b) (a, c))).
        specialize (Har1d1 H).
        eapply Forall2_imply.
        - apply Har1d1.
        - intros.
          destruct a, b.
          destruct H2.
          subst a.
          assumption.
      }
      intros a [r1 d1] [r2 d2] H_in_lac H_in_lab'.
      subst pred.
      pose proof In_combine_Forall2 _ _ _ _ _ H_in_lac Hlac as Har1d1.
      pose proof In_combine_Forall2 _ _ _ _ _ H_in_lab' Hlab' as Har2d2.
      simpl in Har1d1, Har2d2.
      destruct Har1d1 as [H_r1 H_d1].
      destruct Har2d2 as [H_r2 H_d2].
      sets_unfold in H_d1.
      destruct H_d1 as [db' [lbc' [Hdb' [Hlbc' H_sum_bc]]]].

      rewrite H_prob_eq.
      destruct H_sum_bc as [_ H_prob_d1].
      rewrite (H_prob_d1 c).
      rewrite <- sum_map_multi.

      (* make lhs as a sum-map-combine *)
      assert (
        sum
        (map
           (fun a0 : R * Distr C =>
            (da_fg.(prob) a * (let '(r, d) := a0 in r * d.(prob) c))%R)
           lbc')
        =
        sum
        (map
           (fun '(b, (r, d)) =>
            (da_fg.(prob) a * db'.(prob) b * d.(prob) c)%R)
           (combine db'.(pset) lbc'))
      ). {
        f_equal.
        clear H_prob_d1.
        induction Hlbc'.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlbc'.
          destruct y.
          destruct H.
          rewrite H.
          rewrite Rmult_assoc.
          reflexivity.
      }
      rewrite H; clear H.

      (* d2 and db' are equiv *)
      pose proof (g a).(legal).(Legal_unique) _ _ H_d2 Hdb' as H_unique_d2_db'.
      destruct H_unique_d2_db' as [H_prob_d2_db' H_perm_d2_db'].
      clear H_prob_eq.
      assert (d2.(prob) = db'.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
      rewrite H_prob_eq.
      clear H_prob_eq.

      (* similar as the above case,
        now db is bind f g and db' is from (g a).
        so the db.(pset) is a superset of db'.(pset)
        however, as the summed function contains a multiplier of db'.(prob) b0 on rhs,
        it is the same to sum along db'.(pset).
      *)
      remember (fun '(b0, y) =>
      let
      '(_, d) := y in
       (da_fg.(prob) a * db'.(prob) b0 * d.(prob) c)%R) as calc.
      assert (
        exists filtered_dbpset filtered_lbc,
        sum (map calc (combine filtered_dbpset filtered_lbc)) =
        sum (map calc (combine db.(pset) lbc))
        /\ (* All that are left is from d2.(pset). maybe can be replaced by a looser condition (Permutation).  *)
        filtered_dbpset = db'.(pset)
        /\ (* The order is conserved, so any Forall2 preds on this still holds *)
        (forall pred, Forall2 pred db.(pset) lbc -> Forall2 pred filtered_dbpset filtered_lbc)
      ). {
        admit.
      }
      destruct H as [filtered_dbpset [filtered_lbc [H_sum_eq [H_dbpset_eq H_forall2_eq]]]].
      pose proof H_forall2_eq _ Hlbc as Hlbc''; clear H_forall2_eq.
      rewrite <- H_sum_eq.
      clear H_sum_eq.
      subst calc.
      f_equal.
      subst filtered_dbpset.
      apply map_map_eq_Forall2.
      remember (fun a0 b : B * (R * Distr C) =>
      (let
       '(b0, y) := a0 in
        let
        '(_, d) := y in
         (da_fg.(prob) a * db'.(prob) b0 * d.(prob) c)%R) =
      (let
       '(b0, y) := b in
        let
        '(_, d) := y in
         (da_fg.(prob) a * db'.(prob) b0 * d.(prob) c)%R)) as pred.
      enough (
        forall a b c,
        In (a, b) (combine db'.(pset) lbc') ->
        In (a, c) (combine db'.(pset) filtered_lbc) ->
        pred (a, b) (a, c)
      ). {
        pose proof combine_Forall2 db'.(pset) lbc' filtered_lbc as Har1d1.
        specialize (Har1d1 (fun a b c => pred (a, b) (a, c))).
        specialize (Har1d1 H).
        eapply Forall2_imply.
        - apply Har1d1.
        - intros.
          destruct a0, b.
          destruct H2.
          subst b0.
          assumption.
      }
      intros b [r3 d3] [r4 d4] H_in_lbc' H_in_lbc''.
      subst pred.
      pose proof In_combine_Forall2 _ _ _ _ _ H_in_lbc' Hlbc' as Har3d3.
      pose proof In_combine_Forall2 _ _ _ _ _ H_in_lbc'' Hlbc'' as Har4d4.
      simpl in Har3d3, Har4d4.
      destruct Har3d3 as [H_r3 H_d3].
      destruct Har4d4 as [H_r4 H_d4].
      (* d3 and d4 are equiv *)
      pose proof (h b).(legal).(Legal_unique) _ _ H_d3 H_d4 as H_unique_d3_d4.
      destruct H_unique_d3_d4 as [H_prob_d3_d4 _].
      rewrite H_prob_d3_d4.
      reflexivity.
    }
  }
Admitted. (** Level 3 *)

Lemma bind_assoc_event:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M Prop),
  ProbMonad.equiv_event
    (bind (bind f g) h)
    (bind f (fun a => bind (g a) h)).
Proof.
  intros.
  unfold ProbMonad.equiv_event.
  remember (bind (bind f g) h) as bind_fg_h.
  remember (bind f (fun a : A => bind (g a) h)) as bind_f_gh.
  pose proof bind_assoc _ _ _ f g h as H_bind_assoc.
  unfold ProbMonad.equiv in H_bind_assoc.
  sets_unfold in H_bind_assoc.
  pose proof bind_fg_h.(legal).(Legal_exists) as [d Hd].
  exists d, d.
  repeat split.
  - auto.
  - specialize (H_bind_assoc d).
    destruct H_bind_assoc as [? _].
    subst.
    apply H.
    assumption.
  - reflexivity.
Qed. 

Lemma Forall2_singleton_l:
  forall {A B: Type}
         (pred: A -> B -> Prop)
         (lb: list B)
         (a: A),
         Forall2 pred [a] lb -> 
          exists b, lb = [b] /\ pred a b.
Proof.
  intros.
  destruct lb.
  - inversion H.
  - inversion H.
    assert (
      lb = nil
    ). {
      inversion H5.
      reflexivity.
    }
    subst.
    exists b.
    split; auto.
Qed.

Lemma ProbDistr_sum_distr_singleton:
  forall (A: Type)
         (d: Distr A),
  ProbDistr.legal d ->
  ProbDistr.sum_distr [(1%R, d)] d.
Proof.
  intros.
  destruct H.
  split.
  - simpl.
    rewrite app_nil_r.
    apply nodup_perm_filter_dup.
    assumption.
  - intros a.
    simpl.
    lra.
Qed.

Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> ProbMonad.M B),
  bind (ret a) f == f a.
Proof.
  intros.
  unfold ProbMonad.equiv; sets_unfold.
  intros db.
  split.
  {
    intros Hdb.
    unfold bind in *.
    simpl in *.
    unfold ProbMonad.__bind in Hdb.
    destruct Hdb as [da [lab [Hda [Hlab H_sum_lab_db]]]].
    unfold ProbMonad.__ret in Hda.
    sets_unfold in Hda.
    unfold ProbDistr.is_det in Hda.
    destruct Hda as [H_da_singleton [H_da_prob_1 H_da_prob_0]].
    rewrite H_da_singleton in Hlab.
    apply Forall2_singleton_l in Hlab.
    destruct Hlab as [[r db'] [H_lab_singleton H_lab_b]].
    destruct H_lab_b as [H_lab_b H_db'].

    destruct H_sum_lab_db as [H_perm_lab_db H_prob_db].
    subst lab; simpl in *.
    enough (ProbDistr.equiv db db'). {
      pose proof (f a).(legal).(Legal_congr) as H_congr.
      eapply H_congr.
      - symmetry; apply H.
      - assumption. 
    }
    split.
    - intros b.
      rewrite H_lab_b in H_prob_db.
      rewrite H_da_prob_1 in H_prob_db.
      rewrite H_prob_db.
      lra.
    - pose proof (f a).(legal).(Legal_legal) _ H_db' as H_legal.
      destruct H_legal.

      Search filter_dup.
      rewrite H_perm_lab_db.
      rewrite app_nil_r.
      pose proof nodup_perm_filter_dup _ legal_no_dup.
      symmetry; apply H.
  }
  {
    intros Hdb.
    unfold bind in *.
    simpl in *.
    unfold ProbMonad.__bind.
    unfold ProbMonad.__ret.
    sets_unfold.
    pose proof (ret a).(legal) as H_ret_a_legal.
    destruct H_ret_a_legal.
    destruct Legal_exists as [da Hda].
    exists da, [(1%R, db)].
    split.
    - assumption.
    - split.
      2: {
        apply ProbDistr_sum_distr_singleton.
        apply ((f a).(legal).(Legal_legal)).
        assumption.
      }
      unfold ret in Hda.
      simpl in Hda.
      sets_unfold in Hda.
      unfold ProbMonad.__ret in Hda.
      unfold ProbDistr.is_det in Hda.
      destruct Hda as [Hda_singleton [Hda_prob_1 Hda_prob_0]].
      rewrite Hda_singleton.
      constructor; [| simpl; auto].
      split.
      + symmetry; assumption.
      + assumption.
  }
Qed.

Lemma bind_ret_l_event:
  forall (A: Type)
         (a: A)
         (f: A -> ProbMonad.M Prop),
  ProbMonad.equiv_event (bind (ret a) f) (f a).
Admitted. (** Level 3 *)

Lemma bind_ret_r:
  forall (A: Type)
         (f: ProbMonad.M A),
  bind f ret == f.
Admitted. (** Level 3 *)

