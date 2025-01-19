Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ListOperation.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope list.

(* claim forall type A, x,y of A, it holds that {x=y} + {x<>y}. *)
Axiom eq_dec: forall {A: Type} (x y: A), {x = y} + {x <> y}.




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
(** Probability Distribution                             *)
(**                                                      *)
(*********************************************************)

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

(* 
Apply ProDistr.sum_distr to an empty list,
we will get a distribution with empty pset,
and compute_pr will return 0.
*)
Lemma sum_distr_nil_prob_zero:
  forall (ds : Distr Prop),
    ProbDistr.sum_distr [] ds ->
    ProbDistr.compute_pr ds 0.
Proof.
  intros.
  destruct H as [H1 H2].
  simpl in *.
  assert (ds.(pset) = []). {
    unfold empty_set in H1.
    eapply Permutation_nil.
    symmetry; auto.
  }
  unfold ProbDistr.compute_pr.
  rewrite H.
  exists [].
  split; auto.
  - intros.
    split.
    + intros.
      inversion H0.
    + intros.
      destruct H0.
      inversion H0.
  - unfold sum_prob.
    simpl.
    split; auto.
    constructor.
Qed.

(*
If a distribution is legal, then any element not in the pset has probability 0.
*)
Lemma not_in_pset_prob_0:
  forall {A: Type} (d: Distr A) (a: A),
    ProbDistr.legal d ->
    ~ In a d.(pset) ->
    d.(prob) a = 0%R.
Proof.
  intros.
  destruct H.
  destruct (Rge_dec (d.(prob) a) 0).
  - destruct (Rle_dec (d.(prob) a) 0).
    + lra.
    + exfalso.
      assert (d.(prob) a > 0)%R by lra.
      pose proof legal_pset_valid a H.
      contradiction.
  - exfalso.
    pose proof legal_nonneg a.
    contradiction.
Qed.

Definition make_det {A: Type} (a: A): Distr A :=
  {| ProbDistr.prob := fun a' => if eq_dec a a' then 1%R else 0%R;
     ProbDistr.pset := [a] |}.

(*
The distribution generated by make_det is deterministic.
*)
Lemma make_det_is_det:
  forall {A: Type} (a: A),
    ProbDistr.is_det a (make_det a).
Proof.
  intros.
  unfold ProbDistr.is_det.
  split.
  - simpl.
    reflexivity.
  - split.
    + simpl.
      destruct (eq_dec a a).
      reflexivity.
      contradiction.
    + intros.
      simpl.
      destruct (eq_dec a b).
      * subst.
        contradiction.
      * reflexivity.
Qed.

(*
For any combination of list R and list Ditsr, exists sum_distr.
*)
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

(*
For two lists (R * Distr A), if all pairs are equivalent,
then the sum_distr of the two lists are the same.
*)
Lemma sum_distr_congr_1 {A: Type}:
  forall (l1 l2: list (R * Distr A)) (d0: Distr A),
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) l1 l2 ->
    ProbDistr.sum_distr l1 d0 ->
    ProbDistr.sum_distr l2 d0.
Proof.
  intros l1 l2 d H Hl1.
  split.
  {
    destruct Hl1 as [Hl1 _].
    rewrite Hl1.
    clear Hl1.
    remember (fun '(_, d0) => d0.(pset)) as func.
    enough (perm_filter_dup (concat (map func l1)) (concat (map func l2))). {
      unfold perm_filter_dup in *.
      auto.
    }
    apply Permutation_filter_dup_concat_congr.
    induction H as [| [r1 d1] [r2 d2] l1 l2 H IH].
    - simpl.
      constructor.
    - simpl.
      constructor.
      + destruct H.
        subst.
        destruct H0; auto.
      + apply IHIH.
  }
  {
    intros a.
    destruct Hl1 as [_ Hl1].
    rewrite Hl1.
    f_equal.
    clear Hl1.
    induction H as [| [r1 d1] [r2 d2] l1 l2 H IH].
    - simpl.
      reflexivity.
    - simpl.
      f_equal.
      + destruct H.
        destruct H0.
        subst.
        rewrite H0.
        reflexivity.
      + apply IHIH.
  }
Qed.

(*
Same as sum_distr_congr_1, but in the opposite direction.
*)
Lemma sum_distr_congr_2 {A: Type}:
  forall (l1 l2: list (R * Distr A)) (d0: Distr A),
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) l1 l2 ->
    ProbDistr.sum_distr l2 d0 ->
    ProbDistr.sum_distr l1 d0.
Proof.
  intros l1 l2 d H Hl2.
  eapply sum_distr_congr_1; eauto.
  clear Hl2.
  induction H.
  - constructor.
  - constructor.
    + destruct x, y; simpl.
      destruct H.
      split; auto.
      destruct H1; split; auto.
      symmetry; auto.
    + apply IHForall2.
Qed.

(*
Combination of sum_distr_congr_1 and sum_distr_congr_2.
*)
Lemma sum_distr_congr {A: Type}:
  forall (l1 l2: list (R * Distr A)) (d0: Distr A),
    Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ ProbDistr.equiv d1 d2) l1 l2 ->
    ProbDistr.sum_distr l1 d0 <->
    ProbDistr.sum_distr l2 d0.
Proof.
  intros.
  split.
  - apply sum_distr_congr_1; auto.
  - apply sum_distr_congr_2; auto.
Qed.


(* permutation of ds is ok with sum_distr *)
(* export as congr instance *)
#[export] Instance sum_distr_perm {A: Type}:
  Proper (Permutation (A:=(R * Distr A)) ==> eq ==> iff) (@ProbDistr.sum_distr A).
Proof.
  unfold Proper, respectful.
  intros.
  subst.
  split; intros.
  - destruct H0.
    split.
    {
      clear sum_prob_valid.
      rewrite sum_pset_valid.
      clear sum_pset_valid.
      apply perm_filter_dup_concat_perm.
      apply Permutation_map.
      apply H.
    }
    {
      clear sum_pset_valid.
      intros.
      rewrite sum_prob_valid.
      clear sum_prob_valid.
      apply sum_perm.
      apply Permutation_map.
      apply H.
    }
  - destruct H0.
    split.
    {
      clear sum_prob_valid.
      rewrite sum_pset_valid.
      clear sum_pset_valid.
      apply perm_filter_dup_concat_perm.
      apply Permutation_map.
      symmetry.
      apply H.
    }
    {
      clear sum_pset_valid.
      intros.
      rewrite sum_prob_valid.
      clear sum_prob_valid.
      apply sum_perm.
      apply Permutation_map.
      symmetry.
      apply H.
    }
Qed.

(*
For a legal distribution, for any NoDup list l, if pset is a subset of l,
then the sum of probabilities in l is 1.
*)
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

(* Level 1 *)
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


Definition valid_prop_sublist(l t: list Prop): Prop :=
  forall P, In P t <-> In P l /\ P.

(*
All valid_prop_sublists comtain the same elements.
*)
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

(*
Uniqueness of the result of compute_pr.
*)
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


(** Level 1 *)
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

(** Level 1 *)
Theorem ProbDistr_imply_event_refl_setoid:
  forall d1 d2, ProbDistr.equiv_event d1 d2 -> ProbDistr.imply_event d1 d2.
Proof.
  intros.
  unfold ProbDistr.equiv_event, ProbDistr.imply_event in *.
  destruct H as [r1 [r2 [? [? ?]]]].
  exists r1, r2.
  repeat split; auto.
  rewrite H1.
  apply Rle_refl.
Qed.

(** Level 1 *)
#[export] Instance ProbDistr_equiv_equiv {A: Type}:
  Equivalence (@ProbDistr.equiv A).
Proof. 
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

(** Level 1 *)
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

(** Level 1 *)
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

(** Level 1 *)
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

(** Level 1 *)
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

(** Level 1 *)
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

(*
Lemma of Always_conseq.
For any l: list (R * Distr Prop) which satisfies the Forall2 condition,
and d0 is the sum_distr of l, if (Q a) if not in d0.(pset), then any pair (r, d) in l satisfies the condition that r * d.(prob) (Q a) = 0.
*)
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

(*
Lemma of Always_conseq.
For any l: list (R * Distr Prop) which satisfies prob_zero1 condition,
(i.e. for any a in la, if (Q a) if not in d0.(pset), then any pair (r, d) in l satisfies the condition that r * d.(prob) (Q a) = 0),
the sum of (r * d.(prob) (Q a)) in l is 0.
*)
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

(*
Lemma of Always_conseq.
If dA and lQ satisfy the Forall2 condition, dQ is the sum_distr of lQ, and the sum of prob in dA is sum_r,
then the sum of prob in dQ is sum_r.
*)
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

(*
Lemma of Always_conseq.
Construct a list lP of (r, d) pairs, whcih makes dA and lP satisfy the Forall2 condition.
*)
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

(*
Lemma of Always_conseq.
If la and lP satisfy the Forall2 condition, and dA has non-negative probability for all a in la,
then the sum of (r * d0.(prob) (P a)) in lP is non-negative.
*)
Lemma sum_distr_prob_sum_nonneg:
  forall {A: Type} (la: list A) (dA: Distr A) (P: A -> Prop) (lP: list (R * Distr Prop)),
    (* ProbDistr.legal dA -> *)
    (forall a, In a la -> dA.(prob) a >= 0)%R ->
    Forall2
      (fun (a : A) '(r, d0) =>
        r = dA.(prob) a /\
        d0.(pset) = [P a] /\
        d0.(prob) (P a) = 1%R /\
        (forall b : Prop, P a <> b -> d0.(prob) b = 0%R))
      la lP ->
    (* incl la dA.(pset) -> *)
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
      assert (r >= 0)%R. {
        assert (r = dA.(prob) a1) by apply H4.
        assert (In a1 (a1 :: l)). {
          simpl.
          left; auto.
        }
        specialize (H a1 H2).
        lra.
      }
      assert (r * d.(prob) (P a1) >= 0)%R. {
        destruct (eq_dec (P a1) (P a1)) as [Heq | Hneq].
        - assert (d.(prob) (P a1) = 1%R) by apply H4.
          rewrite H2.
          lra.
        - contradiction.
      }
      simpl.
      (* assert (incl l dA.(pset)) as H_incl. {
        pose proof incl_app_inv [a1] l H1 as [_ H_incl].
        auto.
      } *)
      assert (forall a : A, In a l -> (dA.(prob) a >= 0)%R). {
        intros.
        apply H.
        simpl; auto.
      }
      destruct (eq_dec (P a1) (P a)) as [Heq | Hneq].
      * subst.      
        specialize (IH dA P lP' H3 H6 a1).
        rewrite <- Heq.
        lra.
      * specialize (IH dA P lP' H3 H6 a).
        assert (forall b : Prop, P a1 <> b -> d.(prob) b = 0%R) by apply H4.
        specialize (H5 (P a) Hneq).
        rewrite H5.
        lra.
Qed.

(*
Lemma of Always_conseq.
A non-negative list l can be split into a zero list and a positive list.
*)
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

(*
Lemma of Always_conseq.
If dA and lP satisfy the Forall2 condition, dP is the sum_distr of lP, and dA has non-negative probability for all elements in its pset,
then dP has non-negative probability for all elements in its pset.
*)
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
      * specialize (Hprob (P a1)).
        rewrite Heq.
        rewrite Hprob.
        assert (d.(prob) (P a1) = 1%R) by apply H6.
        assert (sum (map (fun '(r0, d0) => r0 * d0.(prob) (P a1)) lP') >= 0)%R. {   
          apply sum_distr_prob_sum_nonneg with (dA := dA) (P := P) (lP := lP') (la := l); auto.
        }
        rewrite H5.
        lra.
      * specialize (Hprob pa).
        rewrite Hprob.
        assert (forall b : Prop, P a1 <> b -> d.(prob) b = 0%R) by apply H6.
        assert (P a1 <> pa) as Hneq' by auto.
        specialize (H5 pa Hneq').
        rewrite H5.
        assert (exists a2, pa = P a2) as [a2 ?]. {
          assert (In pa (filter_dup (concat (map (fun '(_, d) => d.(pset)) ((r, d) :: lP'))))). {
            apply Permutation_in with (l := dP.(pset)); auto.
          }
          apply filter_dup_in in H7.
          (* Search (In _ (concat _)). *)
          apply In_concat_map_exists in H7 as [(r', d') [? ?]].
          pose proof Forall2_in_r_exists _ _ _ H0.
          specialize (H10 (r', d') H7) as [a2 ?].
          exists a2.
          assert (d'.(pset) = [P a2]) by apply H10.
          rewrite H11 in H9.
          simpl in H9.
          destruct H9.
          + auto.
          + contradiction.
        }
        assert (sum (map (fun '(r0, d0) => r0 * d0.(prob) (P a2)) lP') >= 0)%R. {   
          apply sum_distr_prob_sum_nonneg with (dA := dA) (P := P) (lP := lP') (la := l); auto.
        }
        rewrite H7.
        lra.
Qed.

(*
Lemma of Always_conseq.
For any non-negative list l, if the sum of l is positive, then there exists a positive element in l.
*)
Lemma all_nonneg_list_pos_exists_pos_element:
  forall (l: list R),
    (forall r, In r l -> r >= 0)%R ->
    (sum l > 0)%R ->
    exists r_pos, In r_pos l /\ (r_pos > 0)%R.
Proof.
  induction l as [| r l IH].
  - intros.
    simpl in H0.
    lra.
  - intros.
    simpl in H0.
    assert (r >= 0)%R. {
      apply H.
      left; auto.
    }
    destruct (Rlt_dec 0 r).
    + exists r.
      split; auto.
      left; auto.
    + assert (r = 0)%R by lra.
      assert (sum l > 0)%R by lra.
      assert (forall r : R, In r l -> (r >= 0)%R). {
        intros.
        apply H.
        right; auto.
      }
      specialize (IH H4 H3) as [r_pos [Hin Hpos]].
      exists r_pos.
      split; auto.
      right; auto.
Qed.
    
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
  (* Prove the sum_distr of lP is dP *)
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
  (* Prove the Forall2 property for lP *)
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
  (* Prove rP = 1 *)
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
  (* Split dP.(pset) and dQ.(pset) into zeros and positives *)
  pose proof always_conseq_1 dA dP P lP Hproba H2 H_sum_dP as HnonnegP.
  pose proof always_conseq_1 dA dQ Q lQ Hproba Hforall2 H_sum_distr as HnonnegQ.
  pose proof split_zero_and_pos_from_nonneg_list dQ.(pset) dQ.(prob) 1%R HnonnegQ HsumQset1 as [lQzero [lQpos [HpermQ [HzeroQ [HposQ HsumposQ]]]]].
  pose proof split_zero_and_pos_from_nonneg_list dP.(pset) dP.(prob) 1%R HnonnegP HsumPset1 as [lPzero [lPpos [HpermP [HzeroP [HposP HsumposP]]]]].

  assert (incl lPpos ltrueP) as H_inclP. {
    apply sumup_incl with (zero_list := lPzero) (pos_list := lPpos) (l := dP.(pset)) (f := dP.(prob)) (r := 1%R); auto.
    + unfold ProbDistr.pset; simpl.
      apply filter_dup_nodup.
    + lra.
    + destruct HsumP; auto.
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
  (* Prop with positive probability must be true *)
  assert (forall pa, In pa lPpos -> pa) as H_postrueP. {
    intros.
    apply H_inclP in H0.
    specialize (HtrueP pa) as [? _].
    specialize (H1 H0) as [_ ?].
    assumption.
  }
  assert (forall qa, In qa lQpos -> qa) as H_postrueQ. {
    intros.
    assert (In qa (lQzero ++ lQpos)). {
      apply in_or_app.
      right; auto.
    }
    apply Permutation_sym in HpermQ.
    pose proof Permutation_in qa HpermQ H1.
    clear H1.
    destruct (H_sum_distr) as [HQpset HQprob].
    pose proof Permutation_in qa HQpset H3.
    (* Search filter_dup. *)
    pose proof filter_dup_in (concat (map (fun '(_, d) => d.(pset)) lQ)) qa H1.
    (* Search (In _ (concat _)). *)
    pose proof In_concat_map_exists lQ (fun '(_, d) => d.(pset)) qa H4 as [(r, d) [HinlQ Hd]].
    pose proof Forall2_in_r_exists dA.(pset) lQ 
      (fun (a : A) '(r, d) =>
        r = dA.(prob) a /\
        d.(pset) = [Q a] /\
        d.(prob) (Q a) = 1%R /\
        (forall b : Prop, Q a <> b -> d.(prob) b = 0%R)) Hforall2 (r, d) HinlQ
      as [a ?].
    assert (qa = Q a) as Hqa. {
      assert (d.(pset) = [Q a]) by apply H5.
      rewrite H6 in Hd.
      simpl in Hd.
      destruct Hd.
      + subst.
        auto.
      + contradiction.
    }
    subst.
    (* specialize (Himp a).
    subst.
    apply Himp. *)
    (* FIlter out all elements that have the same value after being 
       mapped by Q *)
    set (Qa_eq_list := filter (fun a0 => if eq_dec (Q a) (Q a0) then true else false) dA.(pset)).
    (* exists an a_t that makes both Q a_t and P a_t have positive probability *)
    assert (exists a_t, In a_t Qa_eq_list /\( dP.(prob) (P a_t) > 0)%R) as [a_t [? ?]]. {
      specialize (HposQ (Q a) H0).
      specialize (HQprob (Q a)).
      assert (exists Qa_neq_list, Permutation dA.(pset) (Qa_eq_list ++ Qa_neq_list)) as [Qa_neq_list Hperma]. {
        clear -Qa_eq_list.
        induction dA.(pset) as [| a' l IH].
        - exists [].
          simpl.
          reflexivity.
        - simpl in Qa_eq_list.
          destruct (eq_dec (Q a) (Q a')).
          + destruct IH as [Qa_neq_list ?].
            exists (Qa_neq_list).
            pose proof perm_skip a' H.
            unfold Qa_eq_list.
            rewrite H0.
            reflexivity.      
          + destruct IH as [Qa_neq_list ?].
            exists (a' :: Qa_neq_list).
            pose proof perm_skip a' H.
            unfold Qa_eq_list.
            assert (Permutation (a' :: filter (fun a0 : A => if eq_dec (Q a) (Q a0) then true else false) l ++ Qa_neq_list) (filter (fun a0 : A => if eq_dec (Q a) (Q a0) then true else false) l ++
            a' :: Qa_neq_list)) by apply Permutation_middle.
            rewrite H0.
            assumption.
      }
      pose proof Forall2_perm_l_exists _ _ _ _ Hperma Hforall2 as [lQ' [HpermlQ ?]].
      pose proof Forall2_app_inv_l _ _ H as [lQeq [lQneq [Hforall2Qaeq [Hforall2Qaneq HlQ]]]].
      assert (dQ.(prob) (Q a) = sum (map (fun '(r, d) => (r * d.(prob) (Q a))%R) lQ')). {
        assert (Permutation (map (fun '(r0, d0) => (r0 * d0.(prob) (Q a))%R) lQ) (map (fun '(r0, d0) => (r0 * d0.(prob) (Q a))%R) lQ')). {
          apply Permutation_map.
          assumption.
        }
        assert (sum (map (fun '(r0, d0) => (r0 * d0.(prob) (Q a))%R) lQ) = sum (map (fun '(r0, d0) => (r0 * d0.(prob) (Q a))%R) lQ')). {
          apply sum_congr.
          assumption.
        }
        rewrite <- H7.
        assumption.
      }
      pose proof sum_map_split_two_lists lQ' (fun '(r, d) => r * d.(prob) (Q a))%R lQeq lQneq HlQ as HsumlQ'.
      rewrite HsumlQ' in H6.
      assert ((sum (map (fun '(r, d) => r * d.(prob) (Q a)) lQneq) = 0)%R). {
        assert (forall r0 d0, In (r0, d0) lQneq -> r0 * d0.(prob) (Q a) = 0)%R. {
          intros.
          pose proof Forall2_in_r_exists _ _ _ Hforall2Qaneq (r0, d0) H7 as [a0 ?].
          assert (In a0 Qa_neq_list) by apply H8.
          destruct (eq_dec (Q a0) (Q a)).
          - assert (In a0 dA.(pset)). {
              assert (In a0 (Qa_eq_list ++ Qa_neq_list)). {
                apply in_or_app.
                right; auto.
              }
              apply Permutation_in with (l := Qa_eq_list ++ Qa_neq_list); auto.
              apply Permutation_sym; auto.
            }
            assert (In a0 Qa_eq_list). {
              apply filter_In.
              split; auto.
              destruct (eq_dec (Q a) (Q a0)); auto.
            }
            pose proof f.(legal).(Legal_legal) dA Hda_in_f as H_legal_f.
            destruct H_legal_f as [? _ _ _].
            pose proof Permutation_NoDup Hperma legal_no_dup as Hnodup.
            (* Search NoDup. *)
            pose proof NoDup_app_disjoint _ _ _ Hnodup a0 H11.
            contradiction.
          - assert (forall b : Prop, Q a0 <> b -> d0.(prob) b = 0%R) by apply H8.
            specialize (H10 (Q a) n).
            rewrite H10.
            lra.
        }
        clear - H7.
        induction lQneq as [| [r d] l IH].
        - simpl.
          lra.
        - simpl.
          pose proof H7 r d (or_introl eq_refl) as Hr.
          rewrite Hr.
          assert ((forall (r0 : R) (d0 : Distr Prop), 
            In (r0, d0) l -> (r0 * d0.(prob) (Q a))%R = 0%R)). {
            intros.
            specialize (H7 r0 d0 (or_intror H)).
            auto.
          }
          specialize (IH H).
          lra.
      }
      (* neq list when calculate prob related to Q a, they get 0 *)
      assert (dQ.(prob) (Q a) = sum (map (fun '(r, d) => (r * d.(prob) (Q a))%R) lQeq)). {
        lra.
      }
      assert (forall r, In r (map (fun '(r, d) => (r * d.(prob) (Q a))%R) lQeq) -> r >= 0)%R. {
        intros.
        apply in_map_iff in H9 as [[r' d'] [Heq Hin]].
        pose proof Forall2_in_r_exists Qa_eq_list lQeq
          (fun (a : A) '(r, d0) =>
            r = dA.(prob) a /\
            d0.(pset) = [Q a] /\
            d0.(prob) (Q a) = 1%R /\
            (forall b : Prop, Q a <> b -> d0.(prob) b = 0%R))
          Hforall2Qaeq (r', d') Hin as [a_any Halot].
        assert (r' = dA.(prob) a_any) by apply Halot.
        pose proof f.(legal).(Legal_legal) dA Hda_in_f as H_legal_f.
        destruct H_legal_f as [_ ? _ _].
        specialize (legal_nonneg a_any) as Hnonneg.
        assert (r' >= 0)%R by lra.
        destruct (eq_dec (Q a_any) (Q a)).
        - assert (d'.(prob) (Q a_any) = 1%R) by apply Halot.
          rewrite e in H11.
          rewrite <- Heq.
          rewrite H11.
          lra.
        - assert (forall b : Prop, Q a_any <> b -> d'.(prob) b = 0%R) by apply Halot.
          specialize (H11 (Q a) n).
          rewrite <- Heq.
          rewrite H11.
          lra.
      }
      assert (sum (map (fun '(r, d) => (r * d.(prob) (Q a))%R) lQeq) > 0)%R. {
        lra.
      }
      pose proof all_nonneg_list_pos_exists_pos_element (map (fun '(r, d) => (r * d.(prob) (Q a))%R) lQeq) H9 H10 as [r_pos [H_rpos_in H_rpos]].
      apply in_map_iff in H_rpos_in as [[r' d'] [Heq Hin]].
      pose proof Forall2_in_r_exists Qa_eq_list lQeq
        (fun (a : A) '(r, d0) =>
          r = dA.(prob) a /\
          d0.(pset) = [Q a] /\
          d0.(prob) (Q a) = 1%R /\
          (forall b : Prop, Q a <> b -> d0.(prob) b = 0%R))
        Hforall2Qaeq (r', d') Hin as [a_t Halot].
      assert (r' = dA.(prob) a_t) by apply Halot.
      assert ((r' > 0)%R). {
        destruct (eq_dec (Q a_t) (Q a)).
        - assert (d'.(prob) (Q a_t) = 1%R) by apply Halot.
          rewrite e in H12.
          rewrite H12 in Heq.
          lra.
        - assert (forall b : Prop, Q a_t <> b -> d'.(prob) b = 0%R) by apply Halot.
          specialize (H12 (Q a) n).
          rewrite H12 in Heq.
          lra.
      }
      rewrite H11 in H12.
      (* a_t *)
      exists a_t.
      assert (In a_t dA.(pset)). {
        assert (In a_t Qa_eq_list) by apply Halot.
        assert (In a_t (Qa_eq_list ++ Qa_neq_list)). {
          apply in_or_app.
          left; auto.
        }
        apply Permutation_in with (l := (Qa_eq_list ++ Qa_neq_list)); auto.
        apply Permutation_sym; auto.
      }
      split; auto.
      + apply Halot.
      + simpl.
        unfold dP_prob.
        pose proof In_nth _ a_t a_t H13 as [n [Hn Hnth]].
        
        set (r_t := dA.(prob) a_t).
        set (d_t := nth n lP_d {|
          ProbDistr.prob := fun b : Prop => if eq_dec b (P a_t) then 1%R else 0%R;
          ProbDistr.pset := [P a_t]|}).
        assert (nth n lP (r_t, d_t) = (r_t, d_t)) as HinlP. {
          unfold lP.
          assert (length lP_r = length lP_d). {
            unfold lP_r, lP_d.
            rewrite map_length.
            rewrite map_length.
            reflexivity.
          }
          assert (nth n lP_r r_t = r_t). {
            unfold lP_r, r_t.
            rewrite map_nth.
            rewrite Hnth.
            reflexivity.
          }
          pose proof combine_nth _ _ n r_t d_t H14.
          rewrite H15 in H16.
          assert (length lP_d = length dA.(pset)). {
            unfold lP_d.
            rewrite map_length.
            reflexivity.
          }
          assert (nth n lP_d d_t = d_t). {
            assert (n < length lP_d)%nat. {
              rewrite H17.
              assumption.
            }
            apply nth_indep.
            assumption.
          }
          rewrite H18 in H16.
          assert (length (combine lP_r lP_d) = length lP_d). {
            pose proof combine_length lP_r lP_d.
            rewrite H14 in H19.
            pose proof Min.min_idempotent (length lP_d).
            rewrite H20 in H19.
            assumption.
          }
          assumption.
        }
        pose proof Forall2_to_forall dA.(pset) lP
          (fun (a : A) '(r, d0) =>
            r = dA.(prob) a /\
            d0.(pset) = [P a] /\
            d0.(prob) (P a) = 1%R /\
            (forall b : Prop, P a <> b -> d0.(prob) b = 0%R)) H2.
        pose proof Forall_nth (fun '(a, b) =>
          (fun (a0 : A) '(r, d0) =>
          r = dA.(prob) a0 /\
          d0.(pset) = [P a0] /\
          d0.(prob) (P a0) = 1%R /\
          (forall b0 : Prop, P a0 <> b0 -> d0.(prob) b0 = 0%R)) a b) (combine dA.(pset) lP) as [? _].
        assert (n < length (combine dA.(pset) lP)). {
          rewrite combine_length.
          assert (length dA.(pset) = length lP). {
            pose proof Forall2_same_length _ _ _ H2.
            assumption.
          }
          rewrite <- H16.
          (* Search Init.Nat.min. *)
          pose proof Min.min_idempotent (length dA.(pset)).
          rewrite H17.
          assumption.
        }
        specialize (H15 H14 n (a_t, (r_t, d_t)) H16).
        assert (nth n (combine dA.(pset) lP) (a_t, (r_t, d_t)) = (a_t, (r_t, d_t))) as Hnthn. {
          rewrite combine_nth.
          + rewrite HinlP, Hnth.
            reflexivity.
          + pose proof Forall2_same_length _ _ _ H2.
            assumption.
        }
        rewrite Hnthn in H15.
        assert (In (r_t, d_t) lP). {
          (* Search (nth). *)
          assert (n < length lP)%nat. {
            assert (length lP = length dA.(pset)). {
              pose proof Forall2_same_length _ _ _ H2.
              auto.
            }
            rewrite H17.
            assumption.
          }
          pose proof nth_In lP (r_t, d_t) H17.
          rewrite HinlP in H18.
          assumption.
        }
        pose proof in_exists_remaining_list_perm lP (r_t, d_t) H17 as [lP' ?].
        assert (sum (map (fun '(r0, d0) => r0 * d0.(prob) (P a_t)) lP) = sum (map (fun '(r0, d0) => r0 * d0.(prob) (P a_t)) ((r_t, d_t) :: lP')))%R. {
          apply sum_congr.
          apply (Permutation_map (fun '(r0, d0) => r0 * d0.(prob) (P a_t))%R).
          assumption.
        }
        rewrite H19.
        simpl.
        assert (d_t.(prob) (P a_t) = 1%R) by apply H15.
        rewrite H20.
        assert (r_t = dA.(prob) a_t) by apply H15.
        rewrite H21.
        assert (sum (map (fun '(r0, d0) => r0 * d0.(prob) (P a_t)) lP') >= 0)%R. {
          (* Search Forall2. *)
          pose proof Forall2_perm_r_exists _ _ _ _ H18 H2 as [la [? ?]].
          inversion H23.
          pose proof f.(legal).(Legal_legal) dA Hda_in_f as H_legal_f.
          apply sum_distr_prob_sum_nonneg with (dA := dA) (P := P) (la := l) (lP := lP'); auto.
        }
        lra.
    }
    specialize (H_postrueP (P a_t)) as Hpa.
    assert (Q a = Q a_t). {
      (* Search (filter). *)
      apply filter_In in H.
      destruct H.
      destruct (eq_dec (Q a) (Q a_t)).
      - auto.
      - discriminate H7.
    }
    specialize (Himp a_t).
    rewrite H7.
    apply Himp.
    apply Hpa.
    assert (In (P a_t) dP.(pset)). {
      assert (In a_t dA.(pset)). {
        unfold Qa_eq_list in H.
        apply filter_In in H.
        destruct H.
        assumption.
      }
      simpl.
      unfold dP_pset.
      apply filter_dup_in_inv.
      apply in_map_iff.
      exists a_t.
      split; auto.
    }
    destruct (in_dec eq_dec (P a_t) lPpos) as [Hin | Hnotin].
    + assumption.
    + assert (In (P a_t) (lPzero ++ lPpos)). {
        apply Permutation_in with (l := dP.(pset)); auto.
      }
      assert (In (P a_t) lPzero). {
        apply in_app_or in H9.
        destruct H9.
        + assumption.
        + contradiction.
      }
      specialize (HzeroP (P a_t) H10).
      lra.
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
    assert (NoDup ltrueQ) as HnodupQ by (destruct HsumQ; auto).
    assert (NoDup dQ.(pset)) as HnodupQ'. {
      destruct H_sum_distr as [Hperm_filterdup _].
      rewrite Hperm_filterdup.
      apply filter_dup_nodup.
    }
    specialize (H1 HnodupQ HnodupQ').
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
    assert (NoDup lQpos) as HnodupQpos. {
      destruct H_sum_distr as [Hperm_filterdup _].
      assert (NoDup dQ.(pset)) as HnodupQ'. {
        rewrite Hperm_filterdup.
        apply filter_dup_nodup.
      }
      pose proof Permutation_NoDup HpermQ HnodupQ' as HnodupQ.
      eapply nodup_app_r; eauto.
    }
    assert (NoDup ltrueQ) as HnoduptrueQ. {
      destruct HsumQ.
      assumption.
    }
    specialize (H3 HnodupQpos HnoduptrueQ).
    assumption.
  }
  destruct HsumQ as [HsumQ' _].
  unfold sum_prob in HsumQ'.
  rewrite <- HsumQ'.
  lra.
Qed.

Theorem compute_pr_exists: forall f, exists r, ProbMonad.compute_pr f r.
Proof.
  intros.
  unfold ProbMonad.compute_pr.
  pose proof f.(legal).(Legal_exists) as [d ?].
  pose proof ProbDistr_compute_pr_exists d as [r ?].
  exists r, d.
  tauto.
Qed.

(** Level 2 *)
#[export] Instance ProbMonad_imply_event_refl:
  Reflexive ProbMonad.imply_event.
Proof.
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
  
(** Level 2 *)
Theorem ProbMonad_imply_event_refl_setoid:
  forall d1 d2, ProbMonad.equiv_event d1 d2 -> ProbMonad.imply_event d1 d2.
Proof.
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

(*
ProbDitr.equiv implies ProbDistr.equiv_event
*)
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

(** Level 2 *)
#[export] Instance ProbMonad_imply_event_trans:
  Transitive ProbMonad.imply_event.
Proof.
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
  
(** Level 2 *)
#[export] Instance ProbMonad_equiv_event_equiv:
  Equivalence ProbMonad.equiv_event.
Proof.
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

(** Level 2 *)
#[export] Instance ProbMonad_imply_event_congr:
  Proper (ProbMonad.equiv_event ==>
          ProbMonad.equiv_event ==> iff) ProbMonad.imply_event.
Proof.
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

(** Level 2 *)
#[export] Instance compute_pr_congr:
  Proper (ProbMonad.equiv_event ==> Sets.equiv) ProbMonad.compute_pr.
Proof.
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

(** Level 2 *)
#[export] Instance ProbMonad_bind_congr (A B: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv ==>
          ProbMonad.equiv)
    (@bind _ ProbMonad A B).
Proof.  
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
  
(*
Split the pair equality into two equalities.
*)
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

(*
For any list (R * Distr A), there exists a sum distribution.
*)
Lemma ProbDistr_sum_distr_exists:
  forall {A: Type} (l: list (R * Distr A)),
    exists d, ProbDistr.sum_distr l d.
Proof.
  intros.
  apply sum_distr_exists.
Qed.

(*
  ds1 and ds2 are summed distributions of L1 and L2.
  if L1 and L2 are pairwise imply_event-constrained, and the weight are pairwise equal,
  then ds1 and ds2 are also imply_event-constrained.
*)
Lemma list_forall_imply_event_with_sum_distributions:
  forall (L1 L2 : list (R * Distr Prop)) (ds1 ds2 : Distr Prop),
     Forall2 (fun '(r1, d1) '(r2, d2) => r1 = r2 /\ (r1 >= 0)%R /\ ProbDistr.imply_event d1 d2
     /\ ProbDistr.legal d1 /\ ProbDistr.legal d2) L1 L2
  -> ProbDistr.sum_distr L1 ds1 
  -> ProbDistr.sum_distr L2 ds2
  -> ProbDistr.imply_event ds1 ds2.
Proof.
  intros L1 L2 d1 d2 HL Hsum1 Hsum2.
  unfold ProbDistr.imply_event.
  pose proof ProbDistr_compute_pr_exists d1 as [r1 Hd1].
  pose proof ProbDistr_compute_pr_exists d2 as [r2 Hd2].
  exists r1, r2.
  repeat split; auto.
  destruct Hsum1 as [Hperm1 Hprob1].
  destruct Hsum2 as [Hperm2 Hprob2].
  unfold ProbDistr.compute_pr in *.
  destruct Hd1 as [l1 [Hl1 [Hr1 Hnodup1]]].
  destruct Hd2 as [l2 [Hl2 [Hr2 Hnodup2]]].
  rewrite <- Hr1, <- Hr2.
  unfold sum_prob.
  unfold ProbDistr.imply_event in *.

  assert (d1.(prob) = fun a => sum (map (fun '(r, d) => (r * d.(prob) a)%R) L1)) as Hprob1' by (apply functional_extensionality; auto).
  clear Hprob1.
  assert (d1.(prob) = fun a => sum (map (fun '((r, d), _) => (r * d.(prob) a)%R) (combine L1 L2))) as Hprob1. {
    apply functional_extensionality.
    intros a.
    rewrite Hprob1'.
    f_equal.
    apply map_combine_l.
    apply (F2_sl HL).
  }
  clear Hprob1'.

  assert (d2.(prob) = fun a => sum (map (fun '(r, d) => (r * d.(prob) a)%R) L2)) as Hprob2' by (apply functional_extensionality; auto).
  clear Hprob2.
  assert (d2.(prob) = fun a => sum (map (fun '(_, (r, d)) => (r * d.(prob) a)%R) (combine L1 L2))) as Hprob2. {
    apply functional_extensionality.
    intros a.
    rewrite Hprob2'.
    f_equal.
    apply map_combine_r.
    apply (F2_sl HL).
  }
  clear Hprob2'.
  
  remember (sum (map d1.(prob) l1)) as lhs.
  remember (sum (map d2.(prob) l2)) as rhs.

  rewrite Hprob1 in Heqlhs.
  erewrite sum_map_sum_map in Heqlhs.
  rewrite Hprob2 in Heqrhs.
  erewrite sum_map_sum_map in Heqrhs.
  subst.

  apply sum_map_le_in.
  intros [[ra da] [rb db]] Hin.

  pose proof Forall2_in_combine _ _ _ HL _ _ Hin as H; simpl in H.
  destruct H as [H_eq_r [H_ge_0 H_imp]].
  destruct H_imp as [H_imp [legal_da legal_db]].
  destruct H_imp as [r1 [r2 [Hr1 [Hr2 H_imp]]]].

  repeat rewrite sum_map_multi.
  subst ra.


  enough (sum (map da.(prob) l1) = r1 /\ (sum (map db.(prob) l2)) = r2)%R by (apply Rmult_le_compat_l; lra).
  split.
  {
    clear Hr2 legal_db H_imp.
    unfold ProbDistr.compute_pr in Hr1.
    destruct Hr1 as [l1' [Hl1' [Hr1' Hnodup1']]].
    unfold sum_prob in Hr1'.
    rewrite <- Hr1'.

  (* 
    l1 is all the d1.(pset) props that holds.
    d1.(pset) = all the psets from L1.
    da is from L1.
    so l1 contains all the props that holds for da.
    l1 also contains all the props that holds that are not in da, which will map to 0 with da.(prob).
  *)
    assert (incl l1' l1) as Hincl. {
      unfold incl.
      intros a Hinl1'.
      clear Hprob1 Hprob2 Hperm2.
      (* da is in L1 *)
      pose proof in_combine_l _ _ _ _ Hin.
      assert (incl da.(pset) d1.(pset)) as Hincl. {
        rewrite Hperm1.
        assert (In da.(pset) (map (fun '(_, d) => d.(pset)) L1)).
        {
          apply in_map_iff.
          exists (rb, da).
          split; auto.
        }
        unfold incl.
        intros a0 Hin0.
        rewrite <- filter_dup_in_iff.
        apply in_concat.
        exists da.(pset).
        simpl; auto.
      }
      pose proof Hl1 a.
      pose proof Hl1' a.
      apply H1 in Hinl1'.
      destruct Hinl1' as [Hindapset Haholds].
      apply H0.
      unfold incl in Hincl.
      split; auto.
    }


    pose proof list_partition_in_notin_iff l1' l1 Hincl.
    destruct H as [l1_in [l1_notin [H_partition H]]].
    enough (Permutation l1' l1_in). {
      rewrite <- H_partition.
      rewrite H0.
      rewrite map_app.
      rewrite sum_app.
      enough (sum (map da.(prob) l1_notin) = 0)%R by lra.
      apply sum_map_zero.
      intros.
      assert (In a l1) as Hinl1. {
        rewrite <- H_partition.
        apply in_or_app; auto.
      }
      pose proof H a Hinl1 as [_ Hnotin].
      apply Hnotin in H1.
      pose proof Hl1 a as H_a_in_l1.
      apply H_a_in_l1 in Hinl1.
      destruct Hinl1 as [H_a_in_d1pset Haholds].
      assert (~(In a da.(pset) /\ a)). {
        pose proof Hl1' a.
        tauto.
      }
      unfold not in H2.
      assert (~(In a da.(pset))). {
        intros H3.
        tauto.
      }
      destruct legal_da.
      assert (~(da.(prob) a > 0)%R). {
        pose proof legal_pset_valid a.
        tauto.
      }
      pose proof legal_nonneg a.
      unfold not in H4.
      apply Rnot_gt_le in H4.
      lra.
    }
    apply NoDup_Permutation; auto.
    - eapply nodup_app_l.
      rewrite H_partition.
      apply Hnodup1.
    - intros a.
      split.
      {
        intros Hinl1'.
        assert (In a l1) as Hinl1 by (apply Hincl; auto).
        pose proof H a Hinl1 as [? _].
        tauto.
      }
      {
        intros Hinl1_in.
        assert (In a l1) as Hinl1. {
          rewrite <- H_partition.
          apply in_or_app; auto.
        }
        pose proof H a Hinl1 as [? _].
        tauto.
      }
  }
  {
    clear Hr1 legal_da H_imp.
    unfold ProbDistr.compute_pr in Hr2.
    destruct Hr2 as [l2' [Hl2' [Hr2' Hnodup2']]].
    unfold sum_prob in Hr2'.
    rewrite <- Hr2'.

    assert (incl l2' l2) as Hincl. {
      unfold incl.
      intros a Hinl2'.
      clear Hprob1 Hprob2 Hperm1.
      (* db is in L2 *)
      pose proof in_combine_r _ _ _ _ Hin.
      assert (incl db.(pset) d2.(pset)) as Hincl. {
        rewrite Hperm2.
        assert (In db.(pset) (map (fun '(_, d) => d.(pset)) L2)).
        {
          apply in_map_iff.
          exists (rb, db).
          split; auto.
        }
        unfold incl.
        intros a0 Hin0.
        rewrite <- filter_dup_in_iff.
        apply in_concat.
        exists db.(pset).
        simpl; auto.
      }
      pose proof Hl2 a.
      pose proof Hl2' a.
      apply H1 in Hinl2'.
      destruct Hinl2' as [Hindapset Haholds].
      apply H0.
      unfold incl in Hincl.
      split; auto.
    }

    pose proof list_partition_in_notin_iff l2' l2 Hincl.
    destruct H as [l2_in [l2_notin [H_partition H]]].
    enough (Permutation l2' l2_in). {
      rewrite <- H_partition.
      rewrite H0.
      rewrite map_app.
      rewrite sum_app.
      enough (sum (map db.(prob) l2_notin) = 0)%R by lra.
      apply sum_map_zero.
      intros.
      assert (In a l2) as Hinl2. {
        rewrite <- H_partition.
        apply in_or_app; auto.
      }
      pose proof H a Hinl2 as [_ Hnotin].
      apply Hnotin in H1.
      pose proof Hl2 a as H_a_in_l2.
      apply H_a_in_l2 in Hinl2.
      destruct Hinl2 as [H_a_in_d2pset Haholds].
      assert (~(In a db.(pset) /\ a)). {
        pose proof Hl2' a.
        tauto.
      }
      unfold not in H2.
      assert (~(In a db.(pset))). {
        intros H3.
        tauto.
      }
      destruct legal_db.
      assert (~(db.(prob) a > 0)%R). {
        pose proof legal_pset_valid a.
        tauto.
      }
      pose proof legal_nonneg a.
      unfold not in H4.
      apply Rnot_gt_le in H4.
      lra.
  }
  apply NoDup_Permutation; auto.
  - eapply nodup_app_l.
    rewrite H_partition.
    apply Hnodup2.  
  - intros a.
    split.
    {
      intros Hinl2'.
      assert (In a l2) as Hinl2 by (apply Hincl; auto).
      pose proof H a Hinl2 as [? _].
      tauto.
    }
    {
      intros Hinl2_in.
      assert (In a l2) as Hinl2. {
        rewrite <- H_partition.
        apply in_or_app; auto.
      }
      pose proof H a Hinl2 as [? _].
      tauto.
    }
  }
Qed.

(*
  there are two mappings from X to M Prop, mapG and mapH.
  For each x in X, mapG x implies mapH x.
  pairsG and pairsH are weighted distributions collection of distX and mapG/mapH.
*)
Lemma Forall2_imply_event_pairs :
  forall (X: Type) (distX: Distr X) (mapG mapH: X -> ProbMonad.M Prop)
         (pairsG pairsH: list (R * Distr Prop)),
    ProbDistr.legal distX ->
    (forall x, ProbMonad.imply_event (mapG x) (mapH x)) ->
    Forall2
      (fun x '(rg, dg) => rg = distX.(prob) x /\ dg ∈ (mapG x).(distr))
      distX.(pset) pairsG ->
    Forall2
      (fun x '(rh, dh) => rh = distX.(prob) x /\ dh ∈ (mapH x).(distr))
      distX.(pset) pairsH ->
    Forall2
      (fun '(rG, dG) '(rH, dH) => rG = rH /\ (rG >= 0)%R /\ ProbDistr.imply_event dG dH 
      /\ ProbDistr.legal dG /\ ProbDistr.legal dH
      )
      pairsG pairsH.
Proof.
  intros X distX mapG mapH pairsG pairsH legal_distX Hmono HFg HFh.
  (* We will proceed by induction on HFg, while simultaneously
     matching it with HFh via 'revert ...; induction ...'. *)
  revert pairsH HFh.
  induction HFg; intros.
  - (* Base case: both lists must be empty *)
    inversion HFh. constructor.
  - (* Inductive case: pair up heads, then recurse on tails *)
    inversion HFh; subst.
    constructor.
    + (* Show the heads satisfy rG = rH and an imply_event relation *)
      destruct y  as [rG dG].
      destruct y0 as [rH dH].
      destruct H  as [HG_eq  HG_in].
      destruct H2 as [HH_eq  HH_in].
      split; [|split].
      3: split.
      4: split.
      * (* Show rG = rH by combining HG_eq and HH_eq *)
        rewrite HG_eq, HH_eq. reflexivity.
      * rewrite HG_eq.
        destruct legal_distX.
        apply legal_nonneg.
      * (* Show dG ==> dH using mapG x ==> mapH x and distribution uniqueness *)
        specialize (Hmono x).
        unfold ProbMonad.imply_event in Hmono.
        destruct Hmono as [midG [midH [HmidG [HmidH Himpl]]]].
        (* Use the .(legal).(Legal_unique) property to identify
           dG with midG and dH with midH, then apply congruence. *)
        pose proof ((mapG x).(legal).(Legal_unique) dG midG HG_in HmidG) as HeqG.
        pose proof ((mapH x).(legal).(Legal_unique) dH midH HH_in HmidH) as HeqH.
        apply ProbDistr_equiv_equiv_event in HeqG.
        apply ProbDistr_equiv_equiv_event in HeqH.
        apply ProbDistr_imply_event_congr with midG midH;
          [exact HeqG | exact HeqH | exact Himpl].
      * (* Show dG and dH are legal distributions *)
        exact ((mapG x).(legal).(Legal_legal) _ HG_in).
      * exact ((mapH x).(legal).(Legal_legal) _ HH_in).

    + (* Inductive step on tails *)
      apply IHHFg. exact H4.
Qed.

(*
If two Monads are equivalent, then the result of binding them with the same function is also equivalent.
*)
Lemma bind_equiv_l_congr_1:
  forall {A B: Type} (f1 f2: ProbMonad.M A) (g: A -> ProbMonad.M B),
    ProbMonad.equiv f1 f2 ->
    forall d, d ∈ (ProbMonad.bind f1 g).(distr) ->
              d ∈ (ProbMonad.bind f2 g).(distr).
Proof.
  intros A B f1 f2 g H_equiv d.
  sets_unfold.
  unfold ProbMonad.equiv in H_equiv.
  intros Hd.
  unfold ProbMonad.bind in *; simpl in *.
  unfold ProbMonad.__bind in *.
  destruct Hd as [da [lab [Hda [Hlab H_sum_lab]]]].
  exists da, lab.
  split; auto.
  eapply f2.(legal).(Legal_congr).
  reflexivity.
  apply H_equiv.
  exact Hda.
Qed.

(*
If two Monads are equivalent, then the result of binding them with the same function is also equivalent.
*)
Lemma bind_equiv_l_congr:
  forall {A B: Type} (f1 f2: ProbMonad.M A) (g: A -> ProbMonad.M B),
    ProbMonad.equiv f1 f2 ->
    ProbMonad.equiv (ProbMonad.bind f1 g) (ProbMonad.bind f2 g).
Proof.
  intros A B f1 f2 g H_equiv.
  unfold ProbMonad.equiv in *.
  sets_unfold.
  intros.
  split.
  - apply bind_equiv_l_congr_1; auto.
  - apply bind_equiv_l_congr_1; auto.
    symmetry; auto.
Qed.

(*
  the reverse of definition of bind operation.
  if we can find a distribution d that looks like the result of binding f and g,
  then it is indeed in the binding of f and g.
*)
Lemma ProbDistr_from_bind:
  forall {A B: Type} {f: ProbMonad.M A} {g: A -> ProbMonad.M B}
    {da: Distr A} {lab: list (R * Distr B)} (d: Distr B),
    da ∈ f.(distr) ->
    Forall2 (fun a '(r, d) => r = da.(prob) a /\ d ∈ (g a).(distr)) da.(pset) lab ->
    ProbDistr.sum_distr lab d ->
    d ∈ (ProbMonad.bind f g).(distr).
Proof.
  intros A B f g da lab d.
  intros Hda Hlab H_sum_lab.
  sets_unfold.
  unfold ProbMonad.bind.
  unfold ProbMonad.__bind.
  simpl.
  exists da, lab.
  split; auto.
Qed.

(*
  if dx and dy are equivalent, and we bind them with the same function g,
  the result distributions dsx and dsy are also equivalent.
*)
Lemma bind_congruence_step:
  forall (A: Type) (mx my: ProbMonad.M A) (dx dy: Distr A) (g: A -> ProbMonad.M Prop) 
         (lx ly: list (R * Distr Prop)) (dsx dsy: Distr Prop),
    ProbMonad.equiv mx my ->
    dx ∈ mx.(distr) ->
    dy ∈ my.(distr) ->
    Forall2 (fun a '(r, d) => r = dx.(prob) a /\ d ∈ (g a).(distr)) dx.(pset) lx ->
    Forall2 (fun a '(r, d) => r = dy.(prob) a /\ d ∈ (g a).(distr)) dy.(pset) ly ->
    ProbDistr.sum_distr lx dsx ->
    ProbDistr.sum_distr ly dsy ->
    ProbDistr.equiv dsx dsy.
Proof.
  intros A mx my dx dy g lx ly dsx dsy.
  intros H_equiv dx_in_mx dy_in_my Hlx Hly.
  intros H_sum_lx H_sum_ly.
  assert (dsx ∈ (ProbMonad.bind mx g).(distr)) as Hdx. {
    eapply ProbDistr_from_bind; eauto.
  }
  assert (dsy ∈ (ProbMonad.bind my g).(distr)) as Hdy. {
    eapply ProbDistr_from_bind; eauto.
  }
  assert (ProbMonad.equiv (ProbMonad.bind mx g) (ProbMonad.bind my g)) as H_bind_equiv. {
    apply bind_equiv_l_congr.
    exact H_equiv.
  }
  unfold ProbMonad.equiv in H_bind_equiv.
  assert (dsx ∈ (ProbMonad.bind my g).(distr)) as Hdx'. {
    eapply H_bind_equiv; eauto.
  }
  eapply (ProbMonad.bind my g).(legal).(Legal_unique); eauto.
Qed.


(** Level 2 *)
#[export] Instance ProbMonad_bind_mono_event (A: Type):
Proper
  (ProbMonad.equiv ==>
    pointwise_relation _ ProbMonad.imply_event ==>
    ProbMonad.imply_event)
  (@bind _ ProbMonad A Prop).
Proof.
  unfold Proper, respectful.
  intros dM1 dM2 H_equivDist fM1 fM2 H_imply.
  unfold ProbMonad.imply_event; simpl.
  unfold ProbMonad.__bind.
  unfold pointwise_relation in H_imply.

  (* Obtain witnesses of distributions from dM1 and dM2 *)
  destruct (dM1.(legal).(Legal_exists)) as [dist1 in_dM1].
  destruct (dM2.(legal).(Legal_exists)) as [dist2 in_dM2].

  (* Because dM1 and dM2 are equivalent, dist1 and dist2 must be equivalent *)
  assert (ProbDistr.equiv dist1 dist2) as eqDist12.
  {
    eapply dM1.(legal).(Legal_unique).
    - exact in_dM1.
    - apply H_equivDist.  
      exact in_dM2.
  }

  (* For each element a in dist1, pick a distribution from fM1 a *)
  assert (exists list1,
             Forall2
               (fun a '(r,d) => r = dist1.(prob) a /\ d ∈ (fM1 a).(distr))
               dist1.(pset) list1)
    as [list1 H_list1].
  {
    eapply list_map_forall_exists.
    intros a0.
    destruct (fM1 a0).(legal).(Legal_exists) as [someDist in_fM1].
    exists (dist1.(prob) a0, someDist). 
    split; [reflexivity | exact in_fM1].
  }

  (* For each element a in dist1, pick a distribution from fM2 a *)
  assert (exists list2,
             Forall2
               (fun a '(r,d) => r = dist1.(prob) a /\ d ∈ (fM2 a).(distr))
               dist1.(pset) list2)
    as [list2 H_list2].
  {
    eapply list_map_forall_exists.
    intros a0.
    destruct (fM2 a0).(legal).(Legal_exists) as [someDist in_fM2].
    exists (dist1.(prob) a0, someDist).
    split; [reflexivity | exact in_fM2].
  }

  (* For each element a in dist2, pick a distribution from fM2 a *)
  assert (exists list3,
             Forall2
               (fun a '(r,d) => r = dist2.(prob) a /\ d ∈ (fM2 a).(distr))
               dist2.(pset) list3)
    as [list3 H_list3].
  {
    eapply list_map_forall_exists.
    intros a0.
    destruct (fM2 a0).(legal).(Legal_exists) as [someDist in_fM2].
    exists (dist2.(prob) a0, someDist).
    split; [reflexivity | exact in_fM2].
  }

  (* Build sums from list1, list2, list3 *)
  assert (
    exists dSum1 dSum2 dSum3,
      ProbDistr.sum_distr list1 dSum1 /\
      ProbDistr.sum_distr list2 dSum2 /\
      ProbDistr.sum_distr list3 dSum3
      /\
      ProbDistr.imply_event dSum1 dSum2
      /\ ProbDistr.equiv dSum2 dSum3
  ) as [d1 [d2 [d3 [H_sum1 [H_sum2 [H_sum3 [H_imply12 H_equiv23]]]]]]].
  {
    (* Produce distributions out of list1, list2, list3 *)
    destruct (ProbDistr_sum_distr_exists list1) as [d1x H_d1].
    destruct (ProbDistr_sum_distr_exists list2) as [d2x H_d2].
    destruct (ProbDistr_sum_distr_exists list3) as [d3x H_d3].
    exists d1x, d2x, d3x.
    split; [exact H_d1 |].
    split; [exact H_d2 |].
    split; [exact H_d3 |].
    (* imply_event part from fM1 -> fM2 over the same base dist1 *)
    split.
    - (* show that d1x implies d2x by matching pairs from list1/list2 *)
      eapply list_forall_imply_event_with_sum_distributions with list1 list2.
      ++ apply (Forall2_imply_event_pairs A dist1 fM1 fM2 list1 list2); eauto.
         exact (dM1.(legal).(Legal_legal) _ in_dM1).
      ++ exact H_d1.
      ++ exact H_d2.
    - (* show that d2x and d3x are equivalent, using dist1/dist2 equivalence *)
      eapply (bind_congruence_step _ dM1 dM2 dist1 dist2 fM2 list2 list3 d2x d3x); eauto.
  }

  (* Finally, produce the distributions needed for the main imply_event goal *)
  exists d1, d3.
  split.
  - (* d1 comes from bind dM1 fM1 *)
    exists dist1, list1.
    split; [exact in_dM1 | split; [exact H_list1 | exact H_sum1]].
  - split.
    + (* d3 comes from bind dM2 fM2 *)
      exists dist2, list3.
      split; [exact in_dM2 | split; [exact H_list3 | exact H_sum3]].
    + (* chaining d1 => d2 => d3 to conclude d1 => d3 *)
      eapply ProbDistr_imply_event_trans.
      * exact H_imply12.
      * eapply ProbDistr_imply_event_refl_setoid.
        eapply ProbDistr_equiv_equiv_event.
        exact H_equiv23.
Qed.

(*
If two distributions imply each other, then they are equivalent.
*)
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

(** Level 2 *)
#[export] Instance ProbMonad_bind_congr_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv_event ==>
          ProbMonad.equiv_event)
    (@bind _ ProbMonad A Prop).
Proof.
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

(** Level 2 *)
#[export] Instance ProbMonad_ret_mono_event:
  Proper (Basics.impl ==> ProbMonad.imply_event) ret.
Proof.
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

(*
If two Monads imply each other, then they are equivalent.
*)
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

(** Level 2 *)
#[export] Instance ProbMonad_ret_congr_event:
  Proper (iff ==> ProbMonad.equiv_event) ret.
Proof.
  unfold Proper, respectful.
  intros P Q H.
  destruct H as [Hpq Hqp].
  pose proof ProbMonad_ret_mono_event as Hmono.
  unfold Proper, Basics.impl in Hmono.
  pose proof Hmono P Q Hpq.
  pose proof Hmono Q P Hqp.
  apply ProbMonad_imply_event_equiv_event; auto.
Qed.


Lemma list_pair_partition_l_nodup_incl:
  forall {A B: Type} (l1: list A) (l2: list B) (l1flag: list A),
  NoDup l1flag ->
  NoDup l1 ->
  incl l1flag l1 ->
  forall pred, Forall2 pred l1 l2 -> 
    exists l1t l1o l2t l2o,
    Forall2 pred l1t l2t /\
    Forall2 pred l1o l2o /\
    Permutation (combine l1 l2) ((combine l1t l2t) ++ (combine l1o l2o)) /\
    l1t = l1flag /\
    (forall a, In a l1o -> ~ In a l1flag).
Proof.
  intros A B l1 l2 l1flag H_nodup_l1flag H_nodup_l1 H_incl_l1flag pred H_l.
  pose proof list_pair_partition_l l1 l2 l1flag pred H_l as H_partition.
  destruct H_partition as [l1t [l1o [l2t [l2o H]]]].
  destruct H as [H_t [H_o [H_perm [H_l1t H_l1o]]]].
  pose proof F2_sl H_l as len_l.
  pose proof F2_sl H_t as len_t.
  pose proof F2_sl H_o as len_o.
  pose proof Permutation_combine_cons len_l len_t len_o H_perm as H_perm_combine.
  destruct H_perm_combine as [H_perm_l1 H_perm_l2].
  assert (Permutation l1t l1flag) as H_perm_l1flag. {
    apply NoDup_Permutation.
    - eapply perm_nodup_app_l.
      symmetry.
      apply H_perm_l1.
      exact H_nodup_l1.
    - exact H_nodup_l1flag.
    - intros a.
      split.
      + intros H_in.
        apply H_l1t.
        exact H_in.
      + intros H_in.
        destruct (in_dec eq_dec a l1o) as [H_in_o | H_not_in_o].
        * exfalso.
          apply H_l1o in H_in_o.
          contradiction.
        * unfold incl in H_incl_l1flag.
          pose proof H_incl_l1flag a H_in.
          rewrite H_perm_l1 in H.
          apply in_app_or in H.
          tauto.
  }
  (* now l1t and l1flag are Perm, substitute all l1t *)
  pose proof combine_perm_l_exists l1t l2t l1flag _ H_t H_perm_l1flag as H_perm_combine_l1.
  destruct H_perm_combine_l1 as [l2t' [H_len_l2t' [H_perm_l2t' H_f2_l2t']]].

  exists l1flag, l1o.
  exists l2t', l2o.
  repeat split; auto.
  rewrite H_perm.
  rewrite H_perm_l2t'.
  reflexivity.
Qed.

      

(** Level 3 *)
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
        intros H_c_in_lac.
        pose proof In_concat_map_exists _ _ _ H_c_in_lac as H_c_in_lac_ex.
        clear H_c_in_lac.
        destruct H_c_in_lac_ex as [[r dc'] [H_in_lac' H_in_dc']].
        pose proof Forall2_in_r_exists _ _ _ Hlac _ H_in_lac' as H_lac'.
        destruct H_lac' as [a' [H_in_dapset [_ H2]]].
        destruct H2 as [db' [H_db' [lbc' [H_forall2_bc H_sum_bc]]]].
        destruct H_sum_bc as [H_sum_bc _].

        (* a' in da.(pset), see lab *)
        pose proof Forall2_in_l_exists _ _ _ Hlab _ H_in_dapset as H_lab.
        destruct H_lab as [[rb1 db1] [H_in_lab [_ H_db1]]].

        (* db1 and db' are both from (g a'). *)
        pose proof (g a').(legal).(Legal_unique) _ _ H_db1 H_db' as H_unique_db1_db'.
        destruct H_unique_db1_db' as [_ H_perm_db1_db'].

        (* c is from dc', which is summed from lbc'. therefore there must be some b'
            such that c is from (h b'). *)
        rewrite H_sum_bc in H_in_dc'.
        apply filter_dup_incl in H_in_dc'.
        pose proof In_concat_map_exists _ _ _ H_in_dc' as H_in_dc'_ex.
        clear H_in_dc'.
        destruct H_in_dc'_ex as [[r' dc''] [H_in_lbc' H_in_dc'']].

        pose proof Forall2_in_r_exists _ _ _ H_forall2_bc _ H_in_lbc' as H_lbc'.
        destruct H_lbc' as [b' [H_in_dbpset [_ H_dc''_hb]]].

        (* as db' and db1 are equiv, b' is in db1 *)
        rewrite <-H_perm_db1_db' in H_in_dbpset.

        (* db1 makes up db via lab *)
        assert (In b' db.(pset)) as H_in_dbpset'. {
          rewrite H_sum_ladb.
          rewrite <- filter_dup_incl.
          apply In_in_concat_map.
          exists (rb1, db1).
          split; auto.
        }

        (* b' is in db, so some (h b') will make up dc via lbc *)
        pose proof Forall2_in_l_exists _ _ _ Hlbc _ H_in_dbpset' as H_lbc.
        destruct H_lbc as [[r'' dc'''] [H_in_lbc'' [_ H2]]].
        
        apply In_in_concat_map.
        exists (r'', dc''').
        split; auto.
        (* dc''' and dc'' are all from h b' *)
        pose proof (h b').(legal).(Legal_unique) _ _ H_dc''_hb H2 as H_unique_dc'''_dc''.
        destruct H_unique_dc'''_dc'' as [_ H_perm_dc'''_dc''].
        rewrite <- H_perm_dc'''_dc''.
        assumption.
      }
    }
    {
      intros c.
      destruct H_sum_distr_ladb as [H_perm_ladb H_sum_ladb].
      assert (NoDup db.(pset)) as H_nodup_dbpset. {
        eapply Permutation_NoDup.
        symmetry.
        apply H_perm_ladb.
        apply filter_dup_nodup.
      }
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
        clear H_perm_ladb.
        clear H_nodup_dbpset.
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
        clear H_perm_ladb.
        clear H_nodup_dbpset.
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
        specialize (H0 (F2_sl Hlab)).
        specialize (H0 (F2_sl Hlac)).
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

        assert (incl d1.(pset) db.(pset)) as H_incl_d1_dbpset. 
        {
          unfold incl.
          intros b H_in_d1.
          rewrite H_perm_ladb.
          enough (In b (concat (map (fun '(_, d) => d.(pset)) lab))). {
            pose proof filter_dup_incl (concat (map (fun '(_, d) => d.(pset)) lab)) b.
            tauto.
          }
          apply In_in_concat_map.
          exists (r1, d1).
          split.
          - pose proof in_combine_r _ _ _ _ H_in_lab as H_in_lab'.
            assumption.
          - assumption. 
        }

        (* summing db.(pset) with d1.(prob)
           is equal to summing along the d1.(pset)
           as all those b's not in d1.(pset) get a multiplier of 0.  *)

        remember (fun (a : B) '(r, d) => r = db.(prob) a /\ d ∈ (h a).(distr))
          as pred.

        remember (fun '(b0, y) =>
        let '(_, d) := y in (d1.(prob) b0 * d.(prob) c)%R) as calc.
        assert (
          exists filtered_dbpset filtered_lbc,
          sum (map calc (combine filtered_dbpset filtered_lbc)) =
          sum (map calc (combine db.(pset) lbc))
          /\
          filtered_dbpset = d1.(pset)
          /\ (* The order is conserved, so any Forall2 preds on this still holds *)
          (Forall2 pred db.(pset) lbc -> Forall2 pred filtered_dbpset filtered_lbc)
        ). {
          (* exists (filter (fun '(b0, _) => if in_dec eq_dec b0 d1.(pset) then true else false) (combine db.(pset) lbc)).
          repeat split.
          - pose proof list_partition_in_notin d1.(pset) (map fst (combine db.(pset) lbc)) as H.
            destruct H as [in_part [notin_part]].
            destruct H as [H_comb_perm [H_in H_notin]]. *)
            pose proof list_pair_partition_l_nodup_incl db.(pset) lbc d1.(pset) as H_partition.
            assert (NoDup d1.(pset)) as H_nodup_d1 by
              apply ((g a).(legal).(Legal_legal) _ H_d1).(legal_no_dup).
            specialize (H_partition H_nodup_d1 H_nodup_dbpset).
            specialize (H_partition H_incl_d1_dbpset).
            specialize (H_partition _ Hlbc).
            destruct H_partition as [filtered_dbpset [filteredout_dbpset H_partition]].
            destruct H_partition as [filtered_lbc [filteredout_lbc H_partition]].
            destruct H_partition as [Hfiltered [Hfilteredout H_partition]].
            destruct H_partition as [H_perm_combine [H_filtered_dbpset H_filteredout_dbpset]].

            exists filtered_dbpset, filtered_lbc.
            repeat split; auto.
            rewrite H_perm_combine.
            rewrite map_app.
            rewrite sum_app.
            enough (sum (map calc (combine filteredout_dbpset filteredout_lbc))=0)%R by lra.
            apply sum_map_zero.
            intros [b [r d]] H_in_filteredout.
            subst calc.
            pose proof in_combine_l _ _ _ _ H_in_filteredout as H_in_filterd_out.
            pose proof H_filteredout_dbpset _ H_in_filterd_out as H_notin_d1.
            pose proof not_in_pset_prob_0 _ _ ((g a).(legal).(Legal_legal) _ H_d1) H_notin_d1 as H_prob_0.
            rewrite H_prob_0.
            lra.
        }
        destruct H as [dbpset' [lbc' [H_sum_eq [H_dbpset_eq H_forall2_eq]]]].
        pose proof H_forall2_eq Hlbc as Hlbc'.
        clear H_forall2_eq.
        rewrite <- H_sum_eq.
        clear H_sum_eq.
        subst dbpset'.
        subst calc.
        pose proof combine_permutation_l_exists_holds _ l_sum_to_bc _ _ H_forall2_bc H_perm_ga_d1 as H_perm.
        destruct H_perm as [l_sum_to_bc' [H_perm_l_sum_to_bc [H_perm_combine H_forall2_l_sum_to_bc]]].

        rewrite H_perm_combine.
        f_equal.
        apply map_map_eq_Forall2.
        subst pred.
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
          specialize (H0 (F2_sl Hlbc') (F2_sl H_forall2_l_sum_to_bc)).
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
        intros H_c_in_lbdc.
        pose proof In_concat_map_exists _ _ _ H_c_in_lbdc as H_c_in_lbdc_ex; clear H_c_in_lbdc.
        destruct H_c_in_lbdc_ex as [[rc1 dc1] [H_in_lbdc1 H_in_dc1]].
        (* dc1 is from lbc *)
        pose proof Forall2_in_r_exists _ _ _ Hlbc _ H_in_lbdc1 as H_lbc1.
        destruct H_lbc1 as [b1 [H_in_dbpset [_ H_dc1_hb]]].

        (* db is from bind f g *)
        assert (
          ProbMonad.__bind f.(distr) (fun a : A => (g a).(distr)) db
        ) as Hdb_bind. {
          unfold ProbMonad.bind in fg.
          subst fg.
          simpl in Hdb.
          auto.
        }
        unfold ProbMonad.__bind in Hdb_bind.
        destruct Hdb_bind as [da1 [lab1 [Hda1 [Hlab1 H_sum_distr_lab1db]]]].

        (* b is from db1, so it must be from some (g ?). *)
        destruct H_sum_distr_lab1db as [H_perm_lab1db _].
        rewrite H_perm_lab1db in  H_in_dbpset.
        apply filter_dup_incl in H_in_dbpset.
        pose proof In_concat_map_exists _ _ _ H_in_dbpset as H_in_dbpset_ex.
        clear H_in_dbpset.
        destruct H_in_dbpset_ex as [[rbg dbg] [H_in_lab2 H_in_dc2]].

        pose proof Forall2_in_r_exists _ _ _ Hlab1 _ H_in_lab2 as H_dbg.
        destruct H_dbg as [a1 [H_in_da1pset [_ H_dbg]]].

        (* da and da' are both from f and are thus equiv. unite them first *)
        pose proof f.(legal).(Legal_unique) _ _ Hda Hda1 as H_unique_da_da1.
        destruct H_unique_da_da1 as [H_prob_da_da1 H_perm_da_da1].
        assert (da.(prob) = da1.(prob)) as H_prob_eq by (apply functional_extensionality; auto).
        clear H_prob_da_da1.
        pose proof Forall2_perm_l_exists _ _ _ _ H_perm_da_da1 Hlac as Hlac'.
        destruct Hlac' as [lac' [H_perm_lac_lac' Hlac']].
        rewrite H_perm_lac_lac'.

        (* as a1 is from da, now that da and da' are equiv, we know a1 is here in lac' *)
        pose proof Forall2_in_l_exists _ _ _ Hlac' _ H_in_da1pset as H_lac'.
        simpl in H_lac'.
        destruct H_lac' as [[rc' dc'] [H_in_lac' [_ H_dc']]].
        sets_unfold in H_dc'.
        destruct H_dc' as [db' [lbc' [Hdb' [Hlbc' H_sum_to_dc']]]].

        destruct H_sum_to_dc' as [H_perm_lbc' _].



        (* db' and dbg are all from g a1 and are equiv *)

        pose proof (g a1).(legal).(Legal_unique) _ _ H_dbg Hdb' as H_unique_db'_db1.
        destruct H_unique_db'_db1 as [H_prob_db'_db1 H_perm_db'_db1].
        assert (dbg.(prob) = db'.(prob)) as H_prob_eq2 by (apply functional_extensionality; auto).
        clear H_prob_db'_db1.
        
        (* as b1 is from dbg, now that dbg and db' are equiv, we know b1 is in db' and thus in lbc' *)
        assert (In b1 db'.(pset)) as H_b1_in_db'. {
          symmetry in H_perm_db'_db1.
          rewrite H_perm_db'_db1.
          assumption.
        }
          
        pose proof Forall2_in_l_exists _ _ _ Hlbc' _ H_b1_in_db' as H_lbc'.
        destruct H_lbc' as [[rc'' dc''] [H_in_lbc' [_ H_dc'']]].

        (* dc'' and dc1 are all from h b1 and are equiv *)
        pose proof (h b1).(legal).(Legal_unique) _ _ H_dc'' H_dc1_hb as H_unique_dc''_dc1.
        destruct H_unique_dc''_dc1 as [_ H_perm_dc''_dc1].

        assert (In c dc1.(pset)) as H by assumption.

        apply In_in_concat_map.
        exists (rc', dc').
        split.
        - exact H_in_lac'.
        - rewrite H_perm_lbc'.
          enough (In c (concat (map (fun '(_, d) => d.(pset)) lbc'))). {
            apply filter_dup_in_iff in H0.
            assumption.
          }
          apply In_in_concat_map.
          exists (rc'', dc'').
          split; auto.
          rewrite H_perm_dc''_dc1.
          assumption.
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
      destruct H_sum_lab_db as [H_perm_db H_prob_db].
      assert (NoDup db.(pset)) as H_db_nodup. {
        eapply Permutation_NoDup.
        symmetry. apply H_perm_db.
        apply filter_dup_nodup.
      }
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
        clear H_perm_db.
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
      pose proof combine_permutation_l_exists_holds _ lab _ _ Hlab H_perm_da_da_fg as H_perm.
      destruct H_perm as [lab' [H_perm_lab_lab' [H_perm_comb_comb' H_forall2_comb_comb']]].
      rewrite H_perm_comb_comb' in H_rhs4.
      pose proof H_forall2_comb_comb' as Hlab'.
      clear Hlab.
      clear H_perm_comb_comb'.
      clear H_forall2_comb_comb'.


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
        specialize (Har1d1 (F2_sl Hlac) (F2_sl Hlab')).
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


      assert (
        incl db'.(pset) db.(pset)
      ) as H_db'_incl_db. {
        unfold incl.
        intros b H_in_db'.
        rewrite H_perm_db.
        enough (In b (concat (map (fun '(_, d) => d.(pset)) lab))). {
          apply filter_dup_incl in H.
          assumption.
        }
        apply In_in_concat_map.
        exists (r2, d2).
        rewrite H_perm_lab_lab'.
        split.
        - pose proof in_combine_r _ _ _ _ H_in_lab' as H_in_lab''.
          assumption.
        - rewrite H_perm_d2_db'.
          assumption.
      }
      clear H_perm_lab_lab'.

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

      remember (fun (b : B) '(r, d) => r = db.(prob) b /\ (h b).(distr) d) as pred.
      assert (
        exists filtered_dbpset filtered_lbc,
        sum (map calc (combine filtered_dbpset filtered_lbc)) =
        sum (map calc (combine db.(pset) lbc))
        /\ (* All that are left is from d2.(pset). maybe can be replaced by a looser condition (Permutation).  *)
        filtered_dbpset = db'.(pset)
        /\ (* The order is conserved, so any Forall2 preds on this still holds *)
        (Forall2 pred db.(pset) lbc -> Forall2 pred filtered_dbpset filtered_lbc)
      ). {
        pose proof list_pair_partition_l_nodup_incl db.(pset) lbc as H.
        specialize (H db'.(pset)).
        assert (NoDup db'.(pset)) as H_db'_nodup by
          (apply ((g a).(legal).(Legal_legal) _ Hdb').(legal_no_dup)).
        specialize (H H_db'_nodup); clear H_db'_nodup.
        specialize (H H_db_nodup).
        specialize (H H_db'_incl_db).
        specialize (H _ Hlbc).
        destruct H as [filtered_dbpset [filteredout_dbpset [filtered_lbc [filteredout_lbc H]]]].
        destruct H as [H_filtered [H_filteredout H]].
        destruct H as [H_perm_combine [H_filtered_dbpset H_filteredout_dbpset]].

        exists filtered_dbpset, filtered_lbc.
        repeat split.
        all: auto.
        rewrite H_perm_combine.
        rewrite map_app.
        rewrite sum_app.
        enough (sum (map calc (combine filteredout_dbpset filteredout_lbc)) = 0)%R by lra.
        apply sum_map_zero.
        intros [b0 [r d]] H_in_filteredout.
        subst calc.
        apply in_combine_l in H_in_filteredout.
        pose proof H_filteredout_dbpset _ H_in_filteredout as H_notin_dbpset.
        pose proof (g a).(legal).(Legal_legal) _ Hdb' as H_db'_legal.
        pose proof not_in_pset_prob_0 _ _ H_db'_legal H_notin_dbpset.
        rewrite H.
        lra.
      }
      destruct H as [filtered_dbpset [filtered_lbc [H_sum_eq [H_dbpset_eq H_forall2_eq]]]].
      pose proof H_forall2_eq Hlbc as Hlbc''; clear H_forall2_eq.
      rewrite <- H_sum_eq.
      clear H_sum_eq.
      subst calc.
      f_equal.
      subst filtered_dbpset.
      apply map_map_eq_Forall2.
      subst pred.
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
        specialize (Har1d1 (F2_sl Hlbc') (F2_sl Hlbc'')).
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
Qed.

(** Level 3 *)
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

(*
If a single-element list satisfies the Forall2 condition, then the other list is also a single-element list.
*)
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

(*
A legal distribution can be written as the sum_distr of a single distribution.
*)
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

(** Level 3 *)
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

      (* Search filter_dup. *)
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

(** Level 3 *)
Lemma bind_ret_l_event:
  forall (A: Type)
         (a: A)
         (f: A -> ProbMonad.M Prop),
  ProbMonad.equiv_event (bind (ret a) f) (f a).
Proof.
  intros.
  unfold ProbMonad.equiv_event.
  remember (bind (ret a) f) as bind_ret_f.
  remember (f a) as f_a.
  pose proof bind_ret_l _ _ a f as H_bind_ret_l.
  unfold ProbMonad.equiv in H_bind_ret_l.
  sets_unfold in H_bind_ret_l.
  pose proof bind_ret_f.(legal).(Legal_exists) as [d Hd].
  exists d, d.
  repeat split.
  - auto.
  - specialize (H_bind_ret_l d).
    destruct H_bind_ret_l as [? _].
    subst.
    apply H.
    assumption.
  - reflexivity.
Qed.

(* 
  if the Forall2's pred is strong enough to imply the mapped func,
  then two lists mapped by two funcs are the same.
*)
Lemma Forall2_map_r:
  forall {A B C: Type}
         {pred: A -> B -> Prop}
         {la: list A} {lb: list B}
         (func1 func2: B -> C),
    Forall2 pred la lb ->
    (forall a b, pred a b -> func1 b = func2 b) ->
    map func1 lb = map func2 lb.
Proof.
  intros.
  induction H.
  - simpl. reflexivity.
  - simpl.
    rewrite IHForall2.
    assert (func1 y = func2 y) as H_func_eq. {
      specialize (H0 x y H).
      assumption.
    }
    rewrite H_func_eq.
    reflexivity.
Qed.




(** Level 3 *)
Lemma bind_ret_r:
  forall (A: Type)
         (f: ProbMonad.M A),
  bind f ret == f.
Proof.
  intros.
  unfold ProbMonad.equiv; sets_unfold.
  intros da.
  unfold bind in *; simpl.
  unfold ProbMonad.__bind in *.
  unfold ProbMonad.__ret in *.
  sets_unfold.
  split.
  {
    intros.
    destruct H as [da' [lab [Hda' [Hlab H_sum_lab_db]]]].
    apply f.(legal).(Legal_congr) with da'.
    2: assumption.
    destruct H_sum_lab_db as [H_perm_lab_da H_prob_lab_da].
    split.
    {
      clear H_perm_lab_da.
      intros a.
      rewrite H_prob_lab_da.
      pose proof Forall2_to_forall _ _ _ Hlab as Hlab'.

      (* 
        da'.(pset) may contain a, or may not.
        in both cases, we can filter out what is in da'.(pset) and is not a.
        this part in the sum-map will all be 0, as they can't pass the 'is_det a d' check.
      *)

      destruct (in_dec eq_dec a da'.(pset)) as [H_in | H_not_in].
      {
        (* In a da'.pset
          we can partition da'.pset into two parts: [a] and the rest.
          NoDup da'.pset is used so the rest does not contain a.
        *)
        pose proof f.(legal).(Legal_legal) _ Hda' as H_legal_da'.
        destruct H_legal_da'.

        pose proof NoDup_partition_singleton _ _ legal_no_dup H_in as Hpart.
        destruct Hpart as [filtered_dapset [H_filtered_dapset H_filtered_dapset_no_a]].

        clear Hlab'.
        simpl in H_filtered_dapset.
        (* rearrange the Hlab *)
        pose proof Forall2_perm_l_exists _ _ _ _ H_filtered_dapset Hlab as Hlab_rearrange.
        destruct Hlab_rearrange as [lab_rearrange [H_perm_lab_lab_rearrange Hlab_rearrange]].
        destruct lab_rearrange as [| [r d] lab_rearrange]; [inversion Hlab_rearrange|].
        pose proof Forall2_inv Hlab_rearrange as [Hlab1 Hlab2].
        destruct Hlab1 as [H_r H_det_a_d].
        destruct H_det_a_d as [_ [H_prob_a _]].

        (* sum-map over rearranged lab*)
        rewrite H_perm_lab_lab_rearrange.
        simpl.
        rewrite H_r.
        rewrite H_prob_a.
        enough (sum (map (fun '(r0, d0) => r0 * d0.(prob) a) lab_rearrange) = 0)%R by lra.
        apply sum_map_zero.
        intros [r0 d0] H_in_lab_rearrange.
        pose proof Forall2_in_r_exists _ _ _ Hlab2 _ H_in_lab_rearrange as H_lab_rearrange.
        destruct H_lab_rearrange as [a0 [H_in_filtered_dapset [_ H_d0]]].
        destruct H_d0 as [_ [_ H_prob_zero_d0]].
        specialize (H_prob_zero_d0 a).
        (* a0 is in filterd pset while a is not. so a0<>a *)
        assert (a0 <> a) as H_neq by (intro; subst; contradiction).
        specialize (H_prob_zero_d0 H_neq).
        rewrite H_prob_zero_d0.
        lra.
      }
      {
        (* 
          a is not in da'.pset, which is the same as the above case's second part.
        *)
        pose proof f.(legal).(Legal_legal) _ Hda' as H_legal_da'.
        pose proof not_in_pset_prob_0 _ _ H_legal_da' H_not_in as H_prob_zero.
        rewrite H_prob_zero. clear H_prob_zero.
        symmetry.
        apply sum_map_zero.
        intros [r0 d0] H_in_lab.
        pose proof Forall2_in_r_exists _ _ _ Hlab _ H_in_lab as H_lab.
        destruct H_lab as [a0 [H_in_dapset [_ H_d0]]].
        destruct H_d0 as [_ [_ H_prob_zero_d0]].
        specialize (H_prob_zero_d0 a).
        assert (a0 <> a) as H_neq by (intro; subst; contradiction).
        specialize (H_prob_zero_d0 H_neq).
        rewrite H_prob_zero_d0.
        lra.
      }
    }
    {
      clear H_prob_lab_da.
      rewrite H_perm_lab_da.
      clear H_perm_lab_da.
      assert (
        (map (fun '(_, d) => d.(pset)) lab)
        =
        map (fun x => [x]) da'.(pset)
      ). {
        induction Hlab.
        - simpl. reflexivity.
        - simpl.
          rewrite IHHlab.
          destruct y.
          destruct H.
          destruct H0.
          rewrite H0.
          reflexivity.
      }
      rewrite H; clear H.
      rewrite concat_map_singleton.
      rewrite <- nodup_perm_filter_dup.
      - auto.
      - apply f.(legal).(Legal_legal).
        assumption. 
    }
  }
  {
    intros Hda.
    pose proof f.(legal).(Legal_legal) _ Hda as H_legal_da.
    destruct H_legal_da.
    exists da.
    (* 
      l is a list of singleton prob distr's, each of which is from one element in da.pset.
    *)
    exists (map (fun a => (da.(prob) a, make_det a)) da.(pset)).

    split; auto.
    split.
    {
      clear legal_no_dup.
      clear legal_pset_valid.
      clear legal_prob_1.
      induction da.(pset).
      - simpl. 
        constructor.
      - simpl.
        constructor.
        + split.
          * reflexivity.
          * apply make_det_is_det.
        + apply IHl.
    }
    split.
    {
      clear legal_no_dup.
      clear legal_pset_valid.
      clear legal_prob_1.
      clear legal_nonneg.
      remember (fun '(_, d) => d.(pset)) as get_snd_pset.
      remember (fun a : A => (da.(prob) a, make_det a)) as func.
      rewrite map_map.
      subst.
      assert ((fun x : A => (make_det x).(pset))
              = (fun x : A => [x])) as H. {
        apply functional_extensionality.
        intros a.
        unfold make_det.
        simpl.
        reflexivity.
      }
      rewrite H; clear H.
      rewrite concat_map_singleton.
      rewrite <- nodup_perm_filter_dup.
      - auto.
      - apply f.(legal).(Legal_legal).
        assumption.
    }
    {
      intros a.
      remember (fun '(r, d) => (r * d.(prob) a)%R) as calc_prob.
      remember (fun a0 : A => (da.(prob) a0, make_det a0)) as func.
      rewrite map_map.
      subst.

      (* as the above proof, da.(pset) can be partitioned into
        [a] and the rest (if a is indeed in da.(pset)) or
        only the rest (if a is not in da.(pset)).
      *)

      destruct (in_dec eq_dec a da.(pset)) as [H_in | H_not_in].
      {
        pose proof NoDup_partition_singleton _ _ legal_no_dup H_in as Hpart.
        destruct Hpart as [filtered_dapset [H_filtered_dapset H_filtered_dapset_no_a]].
        rewrite H_filtered_dapset.
        simpl.
        enough (
          sum (map (fun x : A => da.(prob) x * (if eq_dec x a then 1 else 0)) filtered_dapset)
          = 0
        )%R. {
          rewrite H.
          destruct (eq_dec a a) as [_ | H_neq]; [ | contradiction].
          lra.
        }
        apply sum_map_zero.
        intros a0 H_in_filtered_dapset.
        destruct (eq_dec a0 a) as [H_eq | H_neq].
        - subst.
          contradiction.
        - lra.
      }
      {
        pose proof not_in_pset_prob_0 _ _ (f.(legal).(Legal_legal) _ Hda) H_not_in as H_prob_zero.
        rewrite H_prob_zero.
        symmetry.
        apply sum_map_zero.
        intros a0 H_in_lab.
        unfold make_det; simpl.
        destruct (eq_dec a0 a) as [H_eq | H_neq].
        - subst.
          contradiction.
        - lra.
      }
    }
  }
Qed.

(*
  binding with equivalent functions is equivalent.
*)
Lemma bind_equiv_func_r_congr_1:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g1 g2: A -> ProbMonad.M B),
    (forall a, g1 a == g2 a) ->
    forall d,
    d ∈ (bind f g1).(distr) ->
    d ∈ (bind f g2).(distr).
Proof.
  intros.
  unfold bind in *.
  simpl in *.
  unfold ProbMonad.__bind in *.
  destruct H0 as [da [lab [Hda [Hlab H_sum_lab_db]]]].
  sets_unfold.
  exists da, lab.
  split; auto.
  split; auto.
  eapply Forall2_imply.
  apply Hlab.
  intros.
  destruct b.
  split.
  - tauto.
  - destruct H2.
    assert (g1 a == g2 a) as H_g1_g2 by apply H.
    unfold ProbMonad.equiv in H_g1_g2.
    sets_unfold in H_g1_g2.
    apply H_g1_g2.
    assumption.
Qed.

(*
  binding with equivalent functions is equivalent.
*)
Lemma bind_equiv_func_r_congr:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g1 g2: A -> ProbMonad.M B),
    (forall a, g1 a == g2 a) ->
    bind f g1 == bind f g2.
Proof.
  intros.
  unfold ProbMonad.equiv; sets_unfold.
  intros d.
  split.
  - apply bind_equiv_func_r_congr_1; auto.
  - apply bind_equiv_func_r_congr_1; auto.
    symmetry; auto.
Qed.



(** Level 1 *)
Theorem Always_bind_ret {A B: Type}:
  forall (c2: A -> ProbMonad.M B)
         (f: A -> B)
         (P: B -> Prop),
    (forall a, c2 a = ret (f a)) ->
    (forall c1, Always c1 (fun a => P (f a)) <-> Always (a <- c1;; c2 a) P).
Proof.
  intros c2 f P Hc2 c1.
  unfold Always.
  unfold Hoare.
  sets_unfold.
  split.
  {
    intros H a.
    specialize (H a).
    unfold ProbMonad.compute_pr in *.
    intros [d Hd].
    sets_unfold in Hd.
    destruct Hd as [Hd1 Hd2].
    apply H; clear H.
    exists d.
    split; auto.
    clear Hd2.
    sets_unfold.
    assert (c2 = fun a => ret (f a)) as Hc2'. {
      apply functional_extensionality.
      intros.
      apply Hc2.
    }
    subst c2; clear Hc2.
    remember (ProbMonad.bind (ProbMonad.bind c1 (fun a : A => ProbMonad.ret (f a))) (fun res : B => ProbMonad.ret (P res))) as bind1.
    remember (ProbMonad.bind c1 (fun res: A => ProbMonad.ret (P (f res)))) as bind2.
    assert (d ∈ bind1.(distr)) as Hdin1.
    {
      subst bind1.
      subst bind2.
      sets_unfold.
      unfold bind, ret in *; simpl in *.
      unfold ProbMonad.__bind, ProbMonad.__ret in *; simpl in *.
      exact Hd1.
    }
    clear Hd1.
    enough (d ∈ bind2.(distr)) as Hdin2.
    {
      subst bind2.
      sets_unfold.
      unfold bind, ret in *; simpl in *.
      unfold ProbMonad.__bind, ProbMonad.__ret in *; simpl in *.
      exact Hdin2.
    }
    remember (ProbMonad.bind c1 (fun a: A => ProbMonad.bind (ProbMonad.ret (f a)) (fun res: B => ProbMonad.ret (P res))))
     as bind1'.
    assert (bind1 == bind1') as Hbind1eqbind1'.
    {
      subst bind1'.
      subst bind1.
      eapply bind_assoc.
    }
    assert (d ∈ bind1'.(distr)) as Hdin1'.
    {
      unfold ProbMonad.equiv in Hbind1eqbind1'.
      rewrite <- Hbind1eqbind1'.
      exact Hdin1.
    }
    clear bind1 Heqbind1 Hdin1 Hbind1eqbind1'.
    remember (fun res : A => ProbMonad.ret (P (f res))) as func2.
    remember (fun a : A =>
    ProbMonad.bind (ProbMonad.ret (f a))
      (fun res : B => ProbMonad.ret (P res))) as func1'.
    assert (forall a, func1' a == func2 a) as Hfunc1eqfunc2.
    {
      clear a.
      intros.
      subst.
      remember (ProbMonad.bind (ProbMonad.ret (f a))
      (fun res : B => ProbMonad.ret (P res))) as lhs.
      pose proof bind_ret_l _ _ (f a) (fun res : B => ProbMonad.ret (P res)).
      unfold bind, ret in H; simpl in H.
      rewrite <- Heqlhs in H.
      assumption.
    }
    assert (bind1' == bind2). {
      subst.
      eapply bind_equiv_func_r_congr.
      apply Hfunc1eqfunc2.
    }
    sets_unfold.
    unfold ProbMonad.equiv in H.
    sets_unfold in H.
    rewrite <- H.
    exact Hdin1'.
  }
  {
    intros H a.
    specialize (H a).
    unfold ProbMonad.compute_pr in *.
    intros [d Hd].
    sets_unfold in Hd.
    destruct Hd as [Hd1 Hd2].
    apply H; clear H.
    exists d.
    split; auto.
    clear Hd2.
    sets_unfold.
    assert (c2 = fun a => ret (f a)) as Hc2'. {
      apply functional_extensionality.
      intros.
      apply Hc2.
    }
    subst c2; clear Hc2.
    remember (ProbMonad.bind (ProbMonad.bind c1 (fun a : A => ProbMonad.ret (f a))) (fun res : B => ProbMonad.ret (P res))) as bind1.
    remember (ProbMonad.bind c1 (fun res: A => ProbMonad.ret (P (f res)))) as bind2.
    assert (d ∈ bind2.(distr)) as Hdin1.
    {
      subst bind1.
      subst bind2.
      sets_unfold.
      unfold bind, ret in *; simpl in *.
      unfold ProbMonad.__bind, ProbMonad.__ret in *; simpl in *.
      exact Hd1.
    }
    clear Hd1.
    enough (d ∈ bind1.(distr)) as Hdin2.
    {
      subst.
      sets_unfold.
      unfold bind, ret in *; simpl in *.
      unfold ProbMonad.__bind, ProbMonad.__ret in *; simpl in *.
      exact Hdin2.
    }
    remember (ProbMonad.bind c1 (fun a: A => ProbMonad.bind (ProbMonad.ret (f a)) (fun res: B => ProbMonad.ret (P res))))
     as bind1'.
    assert (bind1 == bind1') as Hbind1eqbind1'.
    {
      subst bind1'.
      subst bind1.
      eapply bind_assoc.
    }
    enough (d ∈ bind1'.(distr)) as Hdin1'.
    {
      unfold ProbMonad.equiv in Hbind1eqbind1'.
      sets_unfold in Hbind1eqbind1'.
      apply Hbind1eqbind1'.
      exact Hdin1'.
    }
    clear bind1 Heqbind1 Hbind1eqbind1'.
    remember (fun res : A => ProbMonad.ret (P (f res))) as func2.
    remember (fun a : A =>
    ProbMonad.bind (ProbMonad.ret (f a))
      (fun res : B => ProbMonad.ret (P res))) as func1'.
    assert (forall a, func1' a == func2 a) as Hfunc1eqfunc2.
    {
      clear a.
      intros.
      subst.
      remember (ProbMonad.bind (ProbMonad.ret (f a))
      (fun res : B => ProbMonad.ret (P res))) as lhs.
      pose proof bind_ret_l _ _ (f a) (fun res : B => ProbMonad.ret (P res)).
      unfold bind, ret in H; simpl in H.
      rewrite <- Heqlhs in H.
      assumption.
    }
    assert (bind1' == bind2). {
      subst.
      eapply bind_equiv_func_r_congr.
      apply Hfunc1eqfunc2.
    }
    sets_unfold.
    unfold ProbMonad.equiv in H.
    sets_unfold in H.
    apply H.
    exact Hdin1.
  }
Qed.
