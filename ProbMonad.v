Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import SetsClass.SetsClass.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Logic.Classical_Prop.
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


Lemma perm_filter_dup_cons {A: Type}:
  forall (l l1 l2: list A),
    Permutation (filter_dup l1) (filter_dup l2) ->
    Permutation (filter_dup (l ++ l1)) (filter_dup (l ++ l2)).
Admitted.

Lemma nodup_perm_filter_dup {A: Type}:
  forall (l: list A),
    NoDup l ->
    Permutation l (filter_dup l).
Admitted.

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

(*********************************************************)
(**                                                      *)
(** Probability Distribution                             *)
(**                                                      *)
(*********************************************************)

Definition sum (l: list R): R :=
  fold_right Rplus 0%R l.

Definition sum_prob {A: Type} (pset: list A) (prob: A -> R): R :=
  sum (map prob pset).

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
    forall a, In a d0.(pset) <->
              In a (concat (map (fun '(r, d) => d.(pset)) ds));
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

#[export] Instance sum_prob_congr {A: Type}:
  Proper (Permutation (A:=A) ==> eq ==> eq) (@sum_prob A).
Proof.
  unfold Proper, respectful.
  intros l1 l2 Hl r1 r2 ?.
  subst r2.
  unfold sum_prob.
  enough (Permutation (map r1 l1) (map r1 l2)). {
    apply sum_congr.
    assumption.
  }
  apply perm_map.
  assumption.
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
                  ProbDistr.pset := ga.(pset) ++ d_induction.(pset);
                  ProbDistr.prob := (fun b: B => (da.(prob) a * ga.(prob) b +
                  sum (map (fun '(r, d) => r * d.(prob) b) l_induction))%R )
               |}.
        split; simpl.
        +
          intros b.
          split.
          * apply in_in_app_app.
            intros.
            destruct IH3 as [IH3 _].
            apply IH3.
            auto.
          * apply in_in_app_app.
            intros.
            destruct IH3 as [IH3 _].
            apply IH3.
            auto.
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
    split.
    (* TODO *)
    assert 
    (Forall2 (fun (a : A) '(r, d') => r = da.(prob) a /\ d' ∈ g a) da.(pset) l)
    as H_forall2'. {
      apply H_forall2.
    }
  }
(* Admitted. *)


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

    }
  }


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

Definition Always {A: Type} (c: ProbMonad.M A) (P: A -> Prop): Prop :=
  Hoare (ProbMonad.compute_pr (res <- c;; ret (P res))) (fun pr => pr = 1%R).

Theorem Always_conseq: forall {A: Type} (P Q: A -> Prop),
  (forall a, P a -> Q a) ->
  (forall c, Always c P -> Always c Q).
Admitted. (** Level 1 *)

Theorem Always_bind_ret {A B: Type}:
  forall (c2: A -> ProbMonad.M B)
         (f: A -> B)
         (P: B -> Prop),
    (forall a, c2 a = ret (f a)) ->
    (forall c1, Always c1 (fun a => P (f a)) <-> Always (a <- c1;; c2 a) P).
Proof.
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
Admitted. (** Level 2 *)

Theorem ProbMonad_imply_event_refl_setoid:
  forall d1 d2, ProbMonad.equiv_event d1 d2 -> ProbMonad.imply_event d1 d2.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_equiv_equiv {A: Type}:
  Equivalence (@ProbMonad.equiv A).
Proof.
  unfold ProbMonad.equiv.
  apply equiv_in_domain.
  apply Sets_equiv_equiv.
Qed.

#[export] Instance ProbMonad_imply_event_trans:
  Transitive ProbMonad.imply_event.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_equiv_event_equiv:
  Equivalence ProbMonad.equiv_event.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_imply_event_congr:
  Proper (ProbMonad.equiv_event ==>
          ProbMonad.equiv_event ==> iff) ProbMonad.imply_event.
Admitted. (** Level 2 *)

#[export] Instance compute_pr_congr:
  Proper (ProbMonad.equiv_event ==> Sets.equiv) ProbMonad.compute_pr.
Admitted. (** Level 2 *)

Theorem compute_pr_mono:
  forall f1 f2 r1 r2,
    ProbMonad.compute_pr f1 r1 ->
    ProbMonad.compute_pr f2 r2 ->
    ProbMonad.imply_event f1 f2 ->
    (r1 <= r2)%R.
Admitted.

#[export] Instance ProbMonad_bind_congr (A B: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv ==>
          ProbMonad.equiv)
    (@bind _ ProbMonad A B).
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_bind_mono_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.imply_event ==>
          ProbMonad.imply_event)
    (@bind _ ProbMonad A Prop).
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_bind_congr_event (A: Type):
  Proper (ProbMonad.equiv ==>
          pointwise_relation _ ProbMonad.equiv_event ==>
          ProbMonad.equiv_event)
    (@bind _ ProbMonad A Prop).
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_ret_mono_event:
  Proper (Basics.impl ==> ProbMonad.imply_event) ret.
Admitted. (** Level 2 *)

#[export] Instance ProbMonad_ret_congr_event:
  Proper (iff ==> ProbMonad.equiv_event) ret.
Admitted. (** Level 2 *)

Lemma bind_assoc:
  forall (A B C: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M C),
  bind (bind f g) h ==
  bind f (fun a => bind (g a) h).
Admitted. (** Level 3 *)

Lemma bind_assoc_event:
  forall (A B: Type)
         (f: ProbMonad.M A)
         (g: A -> ProbMonad.M B)
         (h: B -> ProbMonad.M Prop),
  ProbMonad.equiv_event
    (bind (bind f g) h)
    (bind f (fun a => bind (g a) h)).
Admitted. (** Level 3 *)

Lemma bind_ret_l:
  forall (A B: Type)
         (a: A)
         (f: A -> ProbMonad.M B),
  bind (ret a) f == f a.
Admitted. (** Level 3 *)

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

