Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
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

(*********************************************************)
(**                                                      *)
(** List Operation                                       *)
(**                                                      *)
(*********************************************************)

Section filter_dup.

(** filter_dup 
    remove duplicates from a list while preserving the In relation.
*)

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

Lemma filter_dup_cons:
  forall {A: Type} (l: list A) (a: A),
    filter_dup (a :: l) = set_add eq_dec a (filter_dup l).
Proof.
  intros.
  unfold filter_dup.
  simpl.
  reflexivity.
Qed.

Lemma set_add_already_in:
  forall {A: Type} (l: list A) (a: A),
    In a l -> set_add eq_dec a l = l.
Proof.
  intros.
  induction l.
  - contradiction.
  - simpl.
    destruct (eq_dec a a0).
    + subst.
      reflexivity.
    + simpl in H.
      destruct H.
      * subst; contradiction.
      * f_equal.
        apply IHl.
        auto.
Qed.

Lemma set_add_not_in:
  forall {A: Type} (l: list A) (a: A),
    ~ In a l -> set_add eq_dec a l = l ++ [a].
Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    destruct (eq_dec a a0).
    + subst.
      assert (In a0 (a0 :: l)) by apply in_eq.
      contradiction.
    + simpl.
      f_equal.
      apply IHl.
      unfold not.
      intros.
      apply H.
      right.
      auto.
Qed.

Lemma perm_filter_dup_notin:
  forall {A: Type} (l: list A) (a: A),
    ~ In a (filter_dup l) ->
    Permutation (filter_dup (a :: l)) (a :: filter_dup l).
Proof.
  intros.
  rewrite filter_dup_cons.
  rewrite set_add_not_in; auto.
  rewrite Permutation_app_comm.
  simpl; auto.
Qed.

Lemma perm_filter_dup_in:
  forall {A: Type} (l: list A) (a: A),
    In a (filter_dup l) ->
    Permutation (filter_dup (a :: l)) (filter_dup l).
Proof.
  intros.
  rewrite filter_dup_cons.
  rewrite set_add_already_in; auto.
Qed.

Lemma not_in_filter_dup_remove:
  forall {A: Type} (l1 l2: list A) (a: A),
    ~ In a (filter_dup (l1 ++ l2)) -> ~ In a (filter_dup l2).
Proof.
  intros.
  unfold not.
  intros.
  apply H.
  clear H.
  pose proof filter_dup_in _ _ H0.
  apply filter_dup_in_inv.
  apply in_or_app.
  right.
  auto.
Qed.

End filter_dup.

Section Permutation_filter_dup.

(* 
  two lists being permutations of each other after removing duplicates.
*)

(** filter_dup and Permutation  *)

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

Lemma perm_filter_dup_incl_inv{A: Type}:
  forall (l1 l2: list A),
    Permutation (filter_dup l1) (filter_dup l2) ->
    (forall x, In x l1 <-> In x l2).
Proof.
  intros.
  split; intros.
  - apply filter_dup_in.
    rewrite <- H.
    apply filter_dup_in_inv.
    auto.
  - apply filter_dup_in.
    rewrite H.
    apply filter_dup_in_inv.
    auto.
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

Definition perm_filter_dup {A: Type} (l1 l2: list A): Prop :=
  Permutation (filter_dup l1) (filter_dup l2).

#[export] Instance eq_perm_filter_dup {A: Type}:
  Equivalence (@perm_filter_dup A).
Proof.
  unfold perm_filter_dup.
  apply equiv_in_domain.
  split.
  - unfold Reflexive.
    reflexivity.
  - unfold Symmetric.
    symmetry; auto.
  - unfold Transitive.
    intros.
    transitivity y.
    all: auto.
Qed.

Lemma perm_filter_dup_perm {A: Type}:
  forall (l1 l2: list A),
    Permutation l1 l2 ->
    perm_filter_dup l1 l2.
Proof.
  intros.
  apply perm_filter_dup_incl.
  intros.
  split; eapply Permutation_in; [| symmetry]; auto.
Qed.

Lemma perm_filter_dup_app_sym {A: Type}:
  forall (l1 l2: list A),
    perm_filter_dup (l1 ++ l2) (l2 ++ l1).
Proof.
  intros.
  enough (Permutation (l1 ++ l2) (l2 ++ l1)). {
    apply perm_filter_dup_perm.
    auto.
  }
  apply Permutation_app_comm.
Qed.

Lemma perm_filter_dup_app_comm {A: Type}:
  forall (l1 l2 l3: list A),
    perm_filter_dup (l1 ++ l2 ++ l3) ((l1 ++ l2) ++ l3).
Proof.
  intros.
  enough (Permutation (l1 ++ l2 ++ l3) ((l1 ++ l2) ++ l3)). {
    apply perm_filter_dup_perm.
    auto.
  }
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma perm_filter_dup_app_perm_l:
  forall {A: Type} (l1 l2 l0: list A),
    Permutation l1 l2 ->
    perm_filter_dup (l1 ++ l0) (l2 ++ l0).
Proof.
  intros.
  enough (Permutation (l1 ++ l0) (l2 ++ l0)). {
    apply perm_filter_dup_perm.
    auto.
  }
  apply Permutation_app_tail.
  auto.
Qed.

Lemma perm_filter_dup_app_perm_r:
  forall {A: Type} (l1 l2 l0: list A),
    Permutation l1 l2 ->
    perm_filter_dup (l0 ++ l1) (l0 ++ l2).
Proof.
  intros.
  transitivity (l1 ++ l0).
  apply perm_filter_dup_app_sym.
  transitivity (l2 ++ l0).
  apply perm_filter_dup_app_perm_l; auto.
  apply perm_filter_dup_app_sym.
Qed.

Lemma filter_dup_twice:
  forall {A: Type} (l: list A),
    Permutation (filter_dup (filter_dup l)) (filter_dup l).
Proof.
  intros.
  apply perm_filter_dup_incl.
  intros.
  symmetry.
  apply filter_dup_in_iff.
Qed.

Lemma perm_filter_dup_app_filter_dup_r:
  forall {A: Type} (l1 l2: list A),
    perm_filter_dup (l1 ++ l2) (l1 ++ filter_dup l2).
Proof.
  intros.
  induction l1 as [| a l1 IH].
  - simpl.
    unfold perm_filter_dup.
    symmetry.
    apply filter_dup_twice.
  - simpl.
    unfold perm_filter_dup in *.
    pose proof perm_filter_dup_incl_inv _ _ IH as IH0.
    apply perm_filter_dup_incl.
    intros.
    split.
    + intros.
      simpl in H.
      destruct H.
      * subst.
        left.
        reflexivity.
      * right.
        apply IH0.
        auto.
    + intros.
      simpl.
      destruct H.
      * subst.
        left.
        reflexivity.
      * right.
        apply IH0.
        auto.
Qed.

(* 
  Permutation (filter_dup (concat l1)) (filter_dup (concat l2))
  holds if l1 and l2 satisfy the following condition:
  Forall2 (fun lx ly => Permutation lx ly) l1 l2.
*)
Lemma Permutation_filter_dup_concat_congr {A: Type}:
  forall (l1 l2: list (list A)),
    Forall2 (fun a b => Permutation a b) l1 l2 ->
    perm_filter_dup (concat l1) (concat l2).
Proof.
  intros.
  induction H.
  - simpl.
    reflexivity.
  - simpl.
    transitivity (y ++ concat l).
    apply perm_filter_dup_app_perm_l; auto.
    transitivity (y ++ filter_dup (concat l)).
    apply perm_filter_dup_app_filter_dup_r.
    symmetry.
    transitivity (y ++ filter_dup (concat l')).
    apply perm_filter_dup_app_filter_dup_r.
    apply perm_filter_dup_app_perm_r.
    unfold perm_filter_dup in IHForall2.
    symmetry.
    apply IHForall2.
Qed.

Lemma perm_filter_dup_concat_perm:
  forall {A: Type} (l1 l2: list (list A)),
    Permutation l1 l2 ->
    perm_filter_dup (concat l1) (concat l2).
Proof.
  intros.
  induction H.
  - simpl.
    reflexivity.
  - simpl.
    transitivity (x ++ filter_dup (concat l)).
    apply perm_filter_dup_app_filter_dup_r.
    symmetry.
    transitivity (x ++ filter_dup (concat l')).
    apply perm_filter_dup_app_filter_dup_r.
    apply perm_filter_dup_app_perm_r.
    symmetry.
    apply IHPermutation.
  - simpl.
    rewrite perm_filter_dup_app_comm.
    rewrite perm_filter_dup_app_comm at 1.
    transitivity ((y ++ x) ++ filter_dup (concat l)).
    apply perm_filter_dup_app_filter_dup_r.
    transitivity ((x ++ y) ++ filter_dup (concat l)).
    2: symmetry; apply perm_filter_dup_app_filter_dup_r.
    apply perm_filter_dup_app_perm_l.
    apply Permutation_app_comm.
  - transitivity (concat l').
    all: auto.
Qed.

End Permutation_filter_dup.

Section NoDup.

(** NoDup  *)

Lemma NoDup_app_disjoint :
  forall (A : Type) (l1 l2 : list A),
    NoDup (l1 ++ l2) ->
    (forall x, In x l1 -> ~ In x l2).
Proof.
  intros A l1 l2 H.
  intros x Hx_l1 Hx_l2.
  induction l1 as [|h t IH].
  - contradiction.
  - inversion H; subst.
    destruct Hx_l1 as [Hx_l1 | Hx_l1].
    + subst x.
      apply H2. apply in_or_app. right. exact Hx_l2.
    + apply IH.
      * assumption.
      * assumption.
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

End NoDup.

Section Permutation_after_map.

(* 
  two lists being permutations of each other after applying a function.
*)


(** Permutation and map *)

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

End Permutation_after_map.

Section Forall2.

(* 
  properties of Forall2 in addition to those given in Coq standard library.
*)

Lemma Forall2_inv:
  forall {A B: Type}
         {pred: A -> B -> Prop}
         {la: list A} {lb: list B}
         {a: A} {b: B},
    Forall2 pred (a :: la) (b :: lb) ->
    pred a b /\ Forall2 pred la lb.
Proof.
  intros.
  inversion H.
  split; auto.
Qed.

Lemma Forall2_sym:
  forall {A B: Type}
         {pred: A -> B -> Prop}
         {la: list A} {lb: list B},
    Forall2 pred la lb ->
    Forall2 (fun b a => pred a b) lb la.
Proof.
  intros.
  induction H.
  - constructor.
  - constructor; auto.
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

Lemma F2_sl {A B: Type}:
  forall {P: A -> B -> Prop} {l1 l2},
    Forall2 P l1 l2 ->
    length l1 = length l2.
Proof.
  exact Forall2_same_length.
Qed.

Lemma list_map_forall_exists:
  forall {A B: Type} (f: A -> B -> Prop) (l1: list A),
    (forall a, exists b, f a b) -> exists l2, Forall2 f l1 l2.
Proof.
  intros A B f l1 H.
  induction l1 as [| a l1'].
  - exists [].
    constructor.
  - destruct IHl1' as [l2 IH].
    specialize (H a).
    destruct H as [b Hb].
    exists (b :: l2).
    constructor; [tauto | exact IH].
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
  intros.
  pose proof Forall2_to_forall _ _ _ H0.
  rewrite Forall_forall in H1.
  specialize (H1 (a, b) H).
  simpl in *.
  tauto.
Qed.

Lemma Forall2_in_combine:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f l1 l2 ->
    forall a b, In (a, b) (combine l1 l2) -> f a b.
Proof.
  intros.
  induction H.
  - inversion H0.
  - simpl in H0.
    destruct H0.
    + inversion H0.
      subst.
      auto.
    + apply IHForall2 in H0.
      auto.
Qed.

Lemma Forall2_in_combine_inv:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop),
    length l1 = length l2 ->
    (forall a b, In (a, b) (combine l1 l2) -> f a b)
    -> Forall2 f l1 l2.
Proof.
  intros A B l1 l2 f Hlen Hf.
  revert l2 Hlen Hf.
  induction l1 as [| a l1' IH].
  - intros.
    assert (l2 = []) by (destruct l2; auto; inversion Hlen).
    subst.
    constructor.
  - intros.
    destruct l2 as [| b l2'].
    + inversion Hlen.
    + simpl in Hlen.
      inversion Hlen.
      constructor.
      * apply Hf.
        simpl; left; auto.
      * apply IH; auto.
        intros.
        apply Hf.
        simpl; right; auto.
Qed.

Lemma Forall2_app_l_break_r:
  forall {A B: Type} (l1a l1b: list A) (l2: list B) (f: A -> B -> Prop),
    Forall2 f (l1a ++ l1b) l2 ->
    exists l2a l2b,
      l2 = (l2a ++ l2b) /\
      Forall2 f l1a l2a /\
      Forall2 f l1b l2b.
Proof.
  intros.
  revert l2 H.
  induction l1a as [|a l1a' IH].
  - exists [], l2.
    simpl in H.
    split; auto.
  - intros.
    destruct l2 as [|b l2'].
    + simpl in H.
      inversion H.
    + simpl in H.
      inversion H.
      apply IH in H5.
      destruct H5 as [l2a [l2b [Hl2 [Hl2a Hl2b]]]].
      exists (b :: l2a), l2b.
      split; auto.
      rewrite Hl2.
      simpl.
      reflexivity.
Qed. 

Lemma Forall2_app_inv_both:
  forall {A B: Type} (la1 la2: list A) (lb1 lb2: list B) (f: A -> B -> Prop),
    length la1 = length lb1 ->
    Forall2 f (la1 ++ la2) (lb1 ++ lb2) ->
    Forall2 f la1 lb1 /\ Forall2 f la2 lb2.
Proof.
  intros A B la1 la2 lb1 lb2 f Hlen1 Happ.
  pose proof F2_sl Happ as Hlenab.
  repeat rewrite app_length in Hlenab.
  assert (length la2 = length lb2) as Hlen2 by lia.
  clear Hlenab.
  revert lb1 lb2 Hlen1 Hlen2 Happ.
  induction la1 as [| a la1' IH].
  - intros.
    assert (lb1 = []) by (apply length_zero_iff_nil; auto).
    subst.
    split.
    + constructor.
    + auto.
  - intros.
    destruct lb1 as [| b lb1'].
    + inversion Hlen1.
    + simpl in Happ.
      pose proof Forall2_inv Happ as [Hab Happ'].
      assert (length la1' = length lb1') as Hlen1' by 
        (inversion Hlen1; auto).
      specialize (IH _ _ Hlen1' Hlen2 Happ').
      destruct IH as [Hla1 Hla2].
      split.
      * constructor; auto.
      * auto.
Qed.

End Forall2.

Section combine.

(* 
  properties of combine in addition to those given in Coq standard library.
  especially with two lists of same length.
*)

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

Lemma combine_same_length:
  forall {A B: Type} {l1: list A} {l2: list B},
    length l1 = length l2 ->
    length (combine l1 l2) = length l1.
Proof.
  intros.
  revert l2 H.
  induction l1 as [| a l1 IH].
  - intros.
    destruct l2 as [| b l2].
    + reflexivity.
    + inversion H.
  - intros.
    destruct l2 as [| b l2].
    + inversion H.
    + simpl.
      f_equal.
      apply IH.
      simpl in H.
      injection H as H.
      auto.
Qed.

Lemma In_combine_combine_common_l:
  forall {A B C: Type} (l1: list A) (l2: list B) (l3: list C) a a' b c,
    length l1 = length l2 ->
    length l1 = length l3 ->
    In ((a, b), (a', c)) (combine (combine l1 l2) (combine l1 l3)) ->
    a = a'.
Proof.
  intros A B C l1 l2 l3 a a' b c Hlen12 Hlen13 H.
  assert (length (combine l1 l2) = length l1) as Hlen1 by (apply combine_same_length; auto).
  assert (length (combine l1 l3) = length l1) as Hlen2 by (apply combine_same_length; auto).
  assert (length (combine l1 l2) = length (combine l1 l3)) as Hlen by (rewrite Hlen1, Hlen2; auto).
  remember ((a, b), (a, c)) as tuple.
  pose proof In_nth _ _ tuple H as [n [Hn Hnth]].
  pose proof combine_nth as Hcomb.
  destruct tuple as [tl tr].
  pose proof (Hcomb _ _ _ _ n tl tr Hlen) as Hcomb'.
  rewrite Hcomb in Hnth.
  2: auto.
  inversion Hnth.
  destruct tl as [a1 b1].
  destruct tr as [a2 c1].
  pose proof (Hcomb _ _ _ _ n a1 b1 Hlen12) as Hcomb1.
  pose proof (Hcomb _ _ _ _ n a2 c1 Hlen13) as Hcomb2.
  rewrite Hcomb1 in H1.
  rewrite Hcomb2 in H2.
  inversion H1.
  inversion H2.
  clear Hcomb1 Hcomb2 Hcomb Hcomb' H1 H2 H3 H4 H5 H6 Heqtuple Hnth.
  assert (n < length l1) as Hnlen. {
    pose proof combine_same_length Hlen12.
    pose proof combine_same_length Hlen.
    lia.
  }
  apply nth_indep.
  auto.
Qed.


Lemma combine_Forall2:
  forall {A B C: Type} (l1: list A) (l2: list B) (l3: list C) (f: A -> B -> C -> Prop),
    length l1 = length l2 ->
    length l1 = length l3 ->
    (forall a b c,
      In (a, b) (combine l1 l2) ->
      In (a, c) (combine l1 l3) ->
      f a b c ) ->
    Forall2 (fun '(a, b) '(a', c) => a=a' /\ f a b c) (combine l1 l2) (combine l1 l3).
Proof.
  intros.
  apply Forall2_in_combine_inv.
  - repeat rewrite combine_same_length; auto.
  - intros [a b] [a' c] H_in.
    pose proof In_combine_combine_common_l _ _ _ _ _ _ _ H H0 H_in as H_eq.
    split.
    + auto.
    + pose proof in_combine_l _ _ _ _ H_in as H_in1.
      pose proof in_combine_r _ _ _ _ H_in as H_in2.
      rewrite <- H_eq in H_in2.
      apply H1; auto.
Qed.


Lemma app_combine_combine:
  forall {A B: Type} (l1 l3: list A) (l2 l4: list B),
    length l1 = length l2 ->
    length l3 = length l4 ->
    combine (l1 ++ l3) (l2 ++ l4) = (combine l1 l2) ++ (combine l3 l4).
Proof.
  intros.
  revert l3 l2 l4 H H0.
  induction l1 as [| a l1 IH].
  - intros.
    simpl in *.
    assert (l2 = []). { destruct l2; auto. inversion H. }
    subst.
    simpl.
    reflexivity.
  - intros.
    destruct l2 as [| b l2].
    + 
      inversion H.
    + simpl.
      f_equal.
      apply IH.
      * simpl in H.
        injection H as H.
        auto.
      * simpl in H0.
        auto.
Qed.

Lemma combine_fst:
  forall {A B: Type} (l1: list A) (l2: list B),
    length l1 = length l2 ->
    map fst (combine l1 l2) = l1.
Proof.
  intros.
  revert l2 H.
  induction l1 as [| a l1 IH].
  - simpl.
    reflexivity.
  - intros.
    destruct l2 as [| b l2].
    + inversion H.
    + simpl.
      f_equal.
      apply IH.
      simpl in H.
      injection H as H.
      auto.
Qed.

Lemma combine_snd:
  forall {A B: Type} (l1: list A) (l2: list B),
    length l1 = length l2 ->
    map snd (combine l1 l2) = l2.
Proof.
  intros.
  revert l1 H.
  induction l2 as [| a l2 IH].
  - intros.
    simpl.
    assert (l1 = []) by (apply length_zero_iff_nil; auto).
    subst.
    reflexivity.
  - intros.
    destruct l1 as [| b l1].
    + inversion H.
    + simpl.
      f_equal.
      apply IH.
      simpl in H.
      injection H as H.
      auto.
Qed.

Lemma Permutation_combine_cons:
  forall {A B: Type} {la: list A} {lb: list B} {la1 lb1 la2 lb2},
    length la = length lb ->
    length la1 = length lb1 ->
    length la2 = length lb2 ->
    Permutation (combine la lb) ((combine la1 lb1) ++ (combine la2 lb2)) ->
    Permutation la (la1 ++ la2) /\
    Permutation lb (lb1 ++ lb2).
Proof.
  intros.
  erewrite <- app_combine_combine in H2; eauto.
  split.
  - pose proof Permutation_map fst H2.
    erewrite combine_fst in H3; eauto.
    erewrite combine_fst in H3; eauto.
    repeat rewrite app_length.
    lia.
  - pose proof Permutation_map snd H2.
    erewrite combine_snd in H3; eauto.
    erewrite combine_snd in H3; eauto.
    repeat rewrite app_length.
    lia.
Qed.



Lemma Forall2_perm_combine:
  forall {A B: Type} l1 l1' l2 l2' (f: A -> B -> Prop),
    length l1 = length l1' ->
    length l1' = length l2' ->
    Forall2 f l1 l2 ->
    Permutation (combine l1 l2) (combine l1' l2') ->
    Forall2 f l1' l2'.
Proof.
  intros A B l1 l1' l2 l2' f Hlen1 Hlen2 Hf Hperm.
  eapply Forall2_in_combine_inv; eauto.
  intros.
  eapply Forall2_in_combine; eauto.
  rewrite Hperm.
  auto.
Qed.

Lemma list_pair_exists_combine:
  forall {A B: Type} (l: list (A * B)),
    exists la lb,
      l = combine la lb /\
      length la = length lb.
Proof.
  intros.
  exists (map fst l), (map snd l).
  split.
  - induction l as [| [a b] l IH].
    + simpl.
      reflexivity.
    + simpl.
      f_equal; auto.
  - induction l as [| [a b] l IH].
    + simpl.
      reflexivity.
    + simpl.
      f_equal; auto.
Qed.

Lemma In_combine_l_inv:
  forall {A B: Type} (l1: list A) (l2: list B) (a: A),
    length l1 = length l2 ->
    In a l1 ->
    exists b, In (a, b) (combine l1 l2).
Proof.
  intros.
  revert l2 H.
  induction l1 as [| a1 l1 IH].
  - inversion H0.
  - intros.
    destruct l2 as [| b l2].
    + inversion H.
    + simpl in H.
      injection H as H.
      destruct H0.
      * subst.
        exists b.
        simpl.
        auto.
      * specialize (IH H0).
        specialize (IH l2 H).
        destruct IH as [b' Hin].
        exists b'.
        simpl.
        auto.
Qed.

End combine.

Section list_partition_permutation.

(* 
  properties of partitioning a list into two lists based on a condition,
  or permutation of a list with respect to another list.
*)

Lemma Permutation_combine_wrt_left {A B: Type}:
  forall (l1: list A) (l2: list B) (l1': list A),
    length l1 = length l2 ->
    Permutation l1 l1' ->
    exists l2', 
      Permutation l2 l2' /\
      Permutation (combine l1 l2) (combine l1' l2').
Proof.
  intros l1 l2 l1' Hlength12 Hperm.
  revert l2 Hlength12.
  induction Hperm.
  - intros l2 Hlength12.
    assert (l2 = []) by (apply length_zero_iff_nil; auto).
    subst; simpl in *.
    exists [].
    split; auto.
  - intros l2 Hlength12.
    destruct l2 as [| b l2]; [inversion Hlength12|].
    assert (length l = length l2) as Hlength12'.
    {
      simpl in Hlength12.
      lia.
    }
    specialize (IHHperm l2 Hlength12').
    destruct IHHperm as [l2i [Hpermi Hcombinei]].
    exists (b :: l2i).
    split; auto.
    simpl.
    apply perm_skip.
    auto.
  - intros l2 Hlength12.
    destruct l2 as [| b1 l2]; [inversion Hlength12|].
    destruct l2 as [| b2 l2]; [inversion Hlength12|]. 
    assert (length l = length l2) as Hlength12'.
    {
      simpl in Hlength12.
      lia.
    }
    exists (b2 :: b1 :: l2).
    split.
    + constructor.
    + simpl.
      constructor.
  - intros l2 Hlength12.
    pose proof IHHperm1 l2 Hlength12 as [l2i1 [Hpermi1 Hcombinei1]].
    assert (length l' = length l2i1) as Hlength12'.
    {
      rewrite <- Hperm1.
      rewrite <- Hpermi1.
      auto.
    }
    pose proof IHHperm2 l2i1 Hlength12' as [l2i2 [Hpermi2 Hcombinei2]].
    exists l2i2.
    split.
    + transitivity l2i1; auto.
    + transitivity (combine l' l2i1); auto.
Qed.

Lemma list_partition_condition:
  forall {A: Type} (l: list A) (f: A -> bool),
    exists l1 l2,
      Permutation (l1 ++ l2) l /\
      (forall a, In a l1 -> f a = true) /\
      (forall a, In a l2 -> f a = false).
Proof.
  intros.
  exists (filter f l), (filter (fun a => negb (f a)) l).
  split.
  - induction l.
    + simpl.
      reflexivity.
    + simpl.
      destruct (f a).
      * simpl.
        rewrite IHl.
        reflexivity.
      * simpl.
        rewrite Permutation_app_comm.
        simpl.
        apply Permutation_cons; [reflexivity | auto].
        rewrite Permutation_app_comm.
        apply IHl.
  - split; intros.
    + apply filter_In in H.
      destruct H.
      destruct (f a); auto.
    + apply filter_In in H.
      destruct H.
      destruct (f a); auto.
Qed.

Lemma list_partition_in_notin:
  forall {A: Type} (l t: list A),
    exists t1 t2,
      Permutation (t1 ++ t2) t /\
      (forall a, In a t1 -> In a l) /\
      (forall a, In a t2 -> ~ In a l).
Proof.
  intros A l t.
  remember (fun x => if in_dec eq_dec x l then true else false) as f.
  pose proof list_partition_condition t f as [t1 [t2 [Hperm [Ht1 Ht2]]]].
  exists t1, t2.
  split; auto.
  split.
  - intros.
    pose proof Ht1 a H.
    destruct (in_dec eq_dec a l); auto.
    exfalso.
    assert (f a = false) as Hf. {
      subst.
      destruct (in_dec eq_dec a l).
      - contradiction.
      - tauto.
    }
    rewrite Hf in H0.
    discriminate.
  - intros.
    pose proof Ht2 a H.
    destruct (in_dec eq_dec a l); auto.
    exfalso.
    assert (f a = true) as Hf. {
      subst.
      destruct (in_dec eq_dec a l).
      - tauto.
      - contradiction.
    }
    rewrite Hf in H0.
    discriminate.
Qed.

Lemma list_partition_in_notin_iff:
  forall {A: Type} (l t: list A),
    incl l t ->
    exists t1 t2,
      Permutation (t1 ++ t2) t /\
      forall a, In a t ->
      (In a t1 <-> In a l) /\
      (In a t2 <-> ~ In a l).
Proof.
  intros A l t Hincl.
  pose proof list_partition_in_notin l t as [t1 [t2 [Hperm [Ht1 Ht2]]]].
  unfold incl in Hincl.
  exists t1, t2.
  split; auto.
  split.
  - intros.
    split.
    + apply Ht1.
    + intros.
      destruct (in_dec eq_dec a t2).
      * exfalso.
        apply Ht2 in i.
        contradiction.
      * 
        rewrite <- Hperm in H.
        pose proof in_app_or t1 t2 a H as [H1 | H2]; auto.
        contradiction.
  - intros.
    split.
    + apply Ht2.
    + intros.
      destruct (in_dec eq_dec a t1).
      * exfalso.
        apply Ht1 in i.
        contradiction.
      *
        rewrite <- Hperm in H.
        pose proof in_app_or t1 t2 a H as [H1 | H2]; auto.
        contradiction.
Qed.

Lemma list_pair_partition_l:
  forall {A B: Type} (l1: list A) (l2: list B) (l1flag: list A),
  forall pred, Forall2 pred l1 l2 -> 
    exists l1t l1o l2t l2o,
      (* the two parts hold the Forall2 *)
      Forall2 pred l1t l2t /\
      Forall2 pred l1o l2o /\
      (* pairs are moved together *)
      Permutation (combine l1 l2) ((combine l1t l2t) ++ (combine l1o l2o)) /\
      (* partition is make with respect to l1flag *)
      (forall a, In a l1t -> In a l1flag) /\
      (forall a, In a l1o -> ~ In a l1flag).
Proof.
  intros.
  remember (fun x: A * B => let (a, _) := x in if in_dec eq_dec a l1flag then true else false) as f.
  pose proof list_partition_condition (combine l1 l2) f as [lt [lo [Hperm [Hl1t Hl1o]]]].
  pose proof list_pair_exists_combine lt as [l1t [l2t [Hcombt Hlent]]].
  pose proof list_pair_exists_combine lo as [l1o [l2o [Hcombo Hleno]]].

  exists l1t, l1o, l2t, l2o.
  subst lt lo.
  assert (combine l1t l2t ++ combine l1o l2o = combine (l1t ++ l1o) (l2t ++ l2o)) as Hcombt.
  {
    rewrite app_combine_combine; auto.
  }
  rewrite Hcombt in Hperm.
  assert (Forall2 pred (l1t ++ l1o) (l2t ++ l2o)) as Hf.
  {
    eapply Forall2_perm_combine.
    3: apply H.
    pose proof F2_sl H as Hlen12.
    pose proof Permutation_length Hperm as Hlen_to12.
    pose proof combine_same_length Hlent.
    pose proof combine_same_length Hleno.
    pose proof combine_same_length Hlen12.
    pose proof app_length (combine l1t l2t) (combine l1o l2o).
    rewrite Hcombt in H3.
    all: try repeat rewrite app_length.
    all: try lia.
    symmetry; auto.
  }
  repeat split.
  - pose proof Forall2_app_inv_both _ _ _ _ _ Hlent Hf.
    tauto.
  - pose proof Forall2_app_inv_both _ _ _ _ _ Hlent Hf.
    tauto.
  - rewrite <- Hperm.
    rewrite Hcombt.
    reflexivity.
  - intros a H_a_in_l1t.
    pose proof In_combine_l_inv _ _ _ Hlent H_a_in_l1t as [b H_in_comb].
    pose proof Hl1t _ H_in_comb.
    destruct (in_dec eq_dec a l1flag); auto.
    exfalso.
    assert (f (a, b) = false) as Hf'. {
      subst.
      destruct (in_dec eq_dec a l1flag); auto.
      contradiction.
    }
    rewrite Hf' in H0.
    discriminate.
  - intros a H_a_in_l1o.
    pose proof In_combine_l_inv _ _ _ Hleno H_a_in_l1o as [b H_in_comb].
    pose proof Hl1o _ H_in_comb.
    destruct (in_dec eq_dec a l1flag); auto.
    exfalso.
    assert (f (a, b) = true) as Hf'. {
      subst.
      destruct (in_dec eq_dec a l1flag); auto.
    }
    rewrite Hf' in H0.
    discriminate.
Qed.

Lemma NoDup_partition_singleton:
  forall {A: Type} (l: list A) (a: A),
    NoDup l ->
    In a l ->
    exists l', 
      Permutation l ([a] ++ l') /\
      ~ In a l'.
Proof.
  intros.
  pose proof list_partition_in_notin [a] l as [t1 [t2 [? [? ?]]]].
  exists t2.
  pose proof perm_nodup_app_l _ _ _ H1 H.
  pose proof perm_nodup_app_r _ _ _ H1 H.
  assert (t1 = [a]). {
    simpl in *.
    assert (forall a1, In a1 t1 -> a1 = a). {
      intros; pose proof H2 a1 H6.
      destruct H7; auto.
      contradiction.
    }
    destruct t1 as [| a1 t1].
    - (* if t1 is nil, then a must be in t2, which contradicts *) 
      exfalso.
      simpl in H1.
      rewrite <- H1 in H0.
      pose proof H3 _ H0.
      absurd (~ (a = a \/ False)).
      {
        auto.
      }
      assumption.
    - enough (a1 = a /\ t1 = []) as Ht. {
        destruct Ht.
        subst.
        reflexivity.
      }
      assert (a1 = a). {
        pose proof H2 a1 (in_eq a1 t1) as Ht1.
        destruct Ht1; auto.
        contradiction.
      }
      split; auto.
      subst.
      (* NoDup a::t1, so t1 does not contain a *)
      pose proof NoDup_cons_iff a t1 as [? _].
      specialize (H7 H4).
      destruct H7 as [? ?].
      destruct t1 as [| a2 t1].
      + reflexivity.
      + exfalso.
        pose proof H6 a2.
        assert (In a2 (a :: a2 :: t1)). {
          simpl.
          right; left; auto.
        }
        specialize (H9 H10).
        subst.
        absurd (~ In a (a :: t1)). {
          simpl.
          auto.
        }
        assumption.
  }
  subst.
  split.
  - rewrite H1.
    reflexivity.
  - assert (NoDup ([a] ++ t2)) as Ht2. {
      rewrite <- H1 in H.
      assumption.
    }
    simpl in Ht2.
    pose proof NoDup_cons_iff a t2 as [? _].
    specialize (H6 Ht2).
    tauto.
Qed.

Lemma combine_permutation_l_exists_holds:
  forall {A B: Type} (l1: list A) (l2: list B)
    (l1': list A) pred,
    Forall2 pred l1 l2 ->
    Permutation l1 l1' ->
    exists l2',
      Permutation l2 l2' /\
      Permutation (combine l1 l2) (combine l1' l2') /\
      (* Forall2 still holds *)
      Forall2 pred l1' l2'.
Proof.
  intros.
    pose proof Permutation_combine_wrt_left l1 l2 l1' as Hi.
    specialize (Hi (F2_sl H) H0).
    destruct Hi as [l2' [H_perm_l2' H_perm_combine]].
    exists l2'.
    split.
    - auto.
    - split; auto.
      pose proof Permutation_length H_perm_l2'.
      pose proof Permutation_length H0.
      pose proof F2_sl H.
      eapply (Forall2_perm_combine l1 l1' l2 l2'); auto.
      lia.
Qed.

Lemma Forall2_perm_l_exists:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop) (l1': list A),
    Permutation l1 l1' ->
    Forall2 f l1 l2 ->
    exists l2', Permutation l2 l2' /\ Forall2 f l1' l2'.
Proof.
  intros.
  intros.
  pose proof combine_permutation_l_exists_holds l1 l2 l1' f H0 H as [l2' [? [? ?]]].
  exists l2'; repeat split; auto.
Qed.

Lemma Forall2_perm_r_exists:
  forall {A B: Type} (l1: list A) (l2: list B) (f: A -> B -> Prop) (l2': list B),
    Permutation l2 l2' ->
    Forall2 f l1 l2 ->
    exists l1', Permutation l1 l1' /\ Forall2 f l1' l2'.
Proof.
  intros.
  assert (Forall2 (fun b a => f a b) l2 l1) as Hf. {
    apply Forall2_sym; auto.
  }
  pose proof combine_permutation_l_exists_holds _ _ _ _ Hf H as [l1' [? [? ?]]].
  exists l1'; repeat split; auto.
  apply Forall2_sym; auto.
Qed.

Lemma combine_perm_l_exists:
  forall {A B: Type} (l1: list A) (l2: list B) (l1': list A),
  forall pred, 
    Forall2 pred l1 l2 ->
    Permutation l1 l1' ->
    exists l2',
      length l2 = length l2' /\
      Permutation (combine l1 l2) (combine l1' l2') /\
      Forall2 pred l1' l2'.
Proof.
  intros.
  pose proof combine_permutation_l_exists_holds l1 l2 l1' pred H H0 as [l2' [? [? ?]]].
  exists l2'; repeat split; auto.
  apply Permutation_length; auto.
Qed.

End list_partition_permutation.

Section misc.

(** Other lemmas *)

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

Lemma concat_map_singleton:
  forall {A: Type}
         (l: list A),
    concat (map (fun x => [x]) l) = l.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma map_combine_l:
  forall {A B C: Type} (f: A -> C) (l1: list A) (l2: list B),
    length l1 = length l2 ->
    map f l1 = map (fun '(a, _) => f a) (combine l1 l2).
Proof.
  intros.
  revert l2 H.
  induction l1 as [| a l1 IH].
  - intros.
    destruct l2 as [| b l2].
    + reflexivity.
    + inversion H.
  - intros.
    destruct l2 as [| b l2].
    + inversion H.
    + simpl.
      f_equal.
      apply IH.
      simpl in H.
      injection H as H.
      auto.
Qed.

Lemma map_combine_r:
  forall {A B C: Type} (f: B -> C) (l1: list A) (l2: list B),
    length l1 = length l2 ->
    map f l2 = map (fun '(_, b) => f b) (combine l1 l2).
Proof.
  intros.
  revert l2 H.
  induction l1 as [| a l1 IH].
  - intros.
    destruct l2 as [| b l2].
    + reflexivity.
    + inversion H.
  - intros.
    destruct l2 as [| b l2].
    + inversion H.
    + simpl.
      f_equal.
      apply IH.
      simpl in H.
      injection H as H.
      auto.
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

#[export] Instance incl_perm_congr {A: Type}:
  Proper (Permutation (A:=A) ==> Permutation (A:=A) ==> iff) (incl (A:=A)).
Proof.
  unfold Proper, respectful.
  intros.
  unfold incl.
  split; intros.
  - rewrite <- H in H2.
    pose proof H1 _ H2.
    rewrite <- H0.
    auto.
  - rewrite H in H2.
    pose proof H1 _ H2.
    rewrite H0.
    auto.
Qed.

Lemma Permutation_filter_dup_concat_incl:
  forall {A: Type} (l1: list A) (l2: list (list A)),
    Permutation l1 (filter_dup (concat l2)) ->
    (
      forall l, In l l2 -> incl l l1
    ).
Proof.
  intros.
  apply in_listlist_concat_incl in H0.
  rewrite H.
  apply filter_dup_incl_list.
  auto.
Qed.

End misc.

Section sum_prob.


(*********************************************************)
(**                                                      *)
(** Properties of sum                                    *)
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

Lemma sum_map_split_two_lists:
  forall {A: Type} (l: list A) (f: A -> R) (l1 l2: list A),
    l = l1 ++ l2 ->
    (sum (map f l) = sum (map f l1) + sum (map f l2))%R.
Proof.
  intros.
  subst.
  rewrite map_app.
  rewrite sum_app.
  reflexivity.
Qed.

Lemma sum_map_zero:
  forall {A: Type}
         (l: list A)
         (func: A -> R),
    (forall a, In a l -> func a = 0%R) ->
    sum (map func l) = 0%R.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl.
    rewrite H.
    2: {
      left. reflexivity.
    }
    rewrite IHl.
    lra.
    intros.
    apply H.
    right. assumption.
Qed.

Lemma sum_map_ge_zero:
  forall {A: Type}
         (l: list A)
         (func: A -> R),
    (forall a, In a l -> (func a >= 0)%R) ->
    (sum (map func l) >= 0)%R.
Proof.
  intros.
  induction l.
  - simpl. lra.
  - simpl.
    assert (H0: (func a >= 0)%R). {
      apply H.
      left. reflexivity.
    }
    assert (H1: (sum (map func l) >= 0)%R). {
      apply IHl.
      intros.
      apply H.
      right. assumption.
    }
    lra.
Qed.

Lemma sum_map_le_in:
  forall {A: Type} (l: list A) (f1 f2: A -> R),
    (forall a, In a l -> (f1 a <= f2 a)%R) ->
    (sum (map f1 l) <= sum (map f2 l))%R.
Proof.
  intros.
  induction l as [| a l'].
  - simpl. lra.
  - simpl.
    assert (f1 a <= f2 a)%R as Hle by (apply H; simpl; auto).
    enough (sum (map f1 l') <= sum (map f2 l'))%R by lra.
    apply IHl'.
    intros.
    apply H.
    simpl. right. auto.
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

Lemma sum_perm:
  forall (l1 l2: list R),
    Permutation l1 l2 ->
    sum l1 = sum l2.
Proof.
  intros.
  induction H.
  - reflexivity.
  - simpl.
    rewrite IHPermutation.
    reflexivity.
  - simpl.
    lra.
  - rewrite IHPermutation1.
    rewrite IHPermutation2.
    reflexivity.
Qed.

#[export] Instance sum_congr:
  Proper (Permutation (A:=R) ==> eq) sum.
Proof.
  unfold Proper, respectful.
  intros.
  apply sum_perm.
  auto.
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


Lemma nonneg_sublist_sum_le:
  forall {A: Type} (l: list A) (f: A -> R) (r: R) (subl: list A),
    (forall a, In a l -> f a >= 0)%R ->
    sum (map f l) = r ->
    incl subl l ->
    NoDup subl ->
    NoDup l ->
    (sum (map f subl) <= r)%R.
Proof.
  intros.
  pose proof list_partition_in_notin subl l as H_partition.
  destruct H_partition as [l_in [l_notin [H_perm [H_in H_notin]]]].
  subst r.
  rewrite <- H_perm.
  rewrite map_app.
  rewrite sum_app.
  assert (Permutation subl l_in) as H_perm_subl_l_in. {
    unfold incl in H1.
    apply NoDup_Permutation.
    - assumption.
    - eapply perm_nodup_app_l.
      apply H_perm.
      assumption.
    - intros.
      split.
      + intros H_in_subl.
        destruct (in_dec eq_dec x l_notin) as [H_in_notin | H_notin_notin].
        * apply H_notin in H_in_notin.
          contradiction.
        * apply H1 in H_in_subl.
          rewrite <- H_perm in H_in_subl.
          apply in_app_or in H_in_subl.
          destruct H_in_subl; auto; contradiction.
      + intros H_in_l_in.
        apply H_in; auto.
  }
  rewrite H_perm_subl_l_in.
  enough (sum (map f l_notin) >= 0)%R by lra.
  apply sum_map_ge_zero.
  intros.
  assert (In a l). {
    eapply Permutation_in.
    apply H_perm.
    apply in_app_iff.
    auto.
  }
  apply H.
  apply H4.
Qed.

Lemma nonneg_sublist_sum_ge:
  forall {A: Type} (l: list A) (f: A -> R) (r: R) (subl: list A),
    (forall a, In a l -> f a >= 0)%R ->
    sum (map f subl) = r ->
    incl subl l ->
    NoDup subl ->
    NoDup l ->
    (sum (map f l) >= r)%R.
Proof.
  intros.
  pose proof list_partition_in_notin subl l as H_partition.
  destruct H_partition as [l_in [l_notin [H_perm [H_in H_notin]]]].
  unfold incl in *.
  assert (Permutation subl l_in) as H_perm_subl_l_in. {
    apply NoDup_Permutation.
    - assumption.
    - eapply perm_nodup_app_l.
      apply H_perm.
      assumption.
    - intros.
      split.
      + intros H_in_subl.
        destruct (in_dec eq_dec x l_notin) as [H_in_notin | H_notin_notin].
        * apply H_notin in H_in_notin.
          contradiction.
        * apply H1 in H_in_subl.
          rewrite <- H_perm in H_in_subl.
          apply in_app_or in H_in_subl.
          destruct H_in_subl; auto; contradiction.
      + intros H_in_l_in.
        apply H_in; auto.
  }
  rewrite <- H_perm.
  subst.
  rewrite H_perm_subl_l_in.
  rewrite map_app.
  rewrite sum_app.
  enough (sum (map f l_notin) >= 0)%R by lra.
  apply sum_map_ge_zero.
  intros.
  assert (In a l). {
    eapply Permutation_in.
    apply H_perm.
    apply in_app_iff.
    auto.
  }
  apply H.
  apply H4.
Qed.

Lemma sumup_incl:
  forall {A: Type} (zero_list pos_list l: list A) (f: A -> R) (r: R),
    NoDup l ->
    Permutation l (zero_list ++ pos_list) ->
    (forall a, In a zero_list -> f a = 0)%R ->
    (forall a, In a pos_list -> f a > 0)%R ->
    sum (map f pos_list) = r ->
    (r >= 0)%R ->
    (forall subl, NoDup subl -> incl subl l -> (sum (map f subl) = r)%R -> incl pos_list subl).
Proof.
  intros A zero_list pos_list l f r Hnodupl HP Hzero Hpos Hsumpos Hr subl Hnodupsubl Hsubl Hsumsubl.
  unfold incl.
  intros a Ha.
  pose proof Hpos a Ha as Hfapos.
  destruct (in_dec eq_dec a subl) as [Hin | Hnotin].
  + auto.
  + assert (sum (map f (a :: subl)) = (f a) + r)%R. {
      simpl.
      lra.
    }
    assert (forall a : A, In a l -> (f a >= 0)%R). {
      intros.
      destruct (in_dec eq_dec a0 zero_list) as [Hin0 | Hnin0].
      - specialize (Hzero a0 Hin0).
        lra.
      - assert (In a0 (zero_list ++ pos_list)). {
          apply Permutation_in with (l := l); auto.
        }
        apply in_app_or in H1.
        destruct H1.
        + contradiction.
        + specialize (Hpos a0 H1).
          lra.
    }
    assert (sum (map f l) = r). {
      assert (Permutation (map f l) (map f (zero_list ++ pos_list))). {
        apply Permutation_map.
        auto.
      }
      assert (sum (map f l) = sum (map f (zero_list ++ pos_list)))%R. {
        apply sum_congr.
        auto.
      }
      rewrite H2.
      clear - Hzero Hpos Hsumpos.
      induction zero_list as [| a0 zero_list IH].
      + simpl.
        lra.
      + simpl.
        pose proof Hzero a0 (or_introl eq_refl) as Hf0.
        assert (forall a : A, In a zero_list -> f a = 0%R). {
          intros.
          apply Hzero.
          right; auto.
        }
        specialize (IH H).
        lra.
    }
    pose proof nonneg_sublist_sum_le l f r (a :: subl) H0 H1 as Hsumge.
    (* Search incl. *)
    assert (In a l). {
      apply Permutation_in with (l := zero_list ++ pos_list); auto.
      apply Permutation_sym; auto.
      apply in_or_app.
      right; auto.
    }
    pose proof incl_cons H2 Hsubl.
    specialize (Hsumge H3).
    assert (NoDup (a :: subl)) as Hnodupasubl. {
      constructor; auto.
    }
    specialize (Hsumge Hnodupasubl Hnodupl).
    lra.
Qed.

End sum_prob.
