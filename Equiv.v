Set Warnings "-notation-overriden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* PLF Imports *)
Require Import Maps.
Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Theorem aequiv_example :
  aequiv (X - X) 0.
Proof.
  unfold aequiv.
  intros.
  simpl.
  omega.
Qed.

Theorem bequiv_example :
  bequiv (X - X = 0) true.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

(* Simple Examples *)

Theorem skip_left : forall c,
  cequiv
    (SKIP;; c)
    c.
Proof.
  unfold cequiv.
  intros.
  split; intros H.
  - inversion H; subst. inversion H2; subst. assumption.
  - apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

(* Exercise: 2 stars (skip_right) *)

Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  unfold cequiv.
  intros c st st'.
  split; intros H.
  - inversion H; subst. inversion H5; subst. assumption.
  - apply E_Seq with st'.
    + assumption.
    + apply E_Skip.
Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2 st st'.
  split; intros H.
  - inversion H; subst; try auto.
    + inversion H5.
  - apply E_IfTrue; try auto.
Qed.

(*
Theorem: If b is equivalent to BTrue, then IFB b THEN c1 ELSE c2 FI is equivalent to c1

Proof.
  * -> We must show that for all st and st', that if IFB b THEN c1 ELSE c2 FI / st \\ st' then c1 / st \\ st'.

  Proceed by cases on the rules that could have been possibly used to show IFB b THEN c1 ELSE c2 FI / st \\ st', namely E_IfTrue and E_IfFalse.

  - Suppose the final rule in the derivation of IFB b THEN c1 ELSE c2 FI / st \\ st' was E_IfTrue. We then have, by the premises of E_IfTrue, that c1 / st \\ st'. This is exactly what we set out to prove.

  - On the other hand, suppose the final rule of the derivation of IFB b THEN c1 ELSE c2 FI / st \\ st' was E_IfFalse. We then know that beval st b = false and c2 / st \\ st'.
   Recall that b is equivalent to BTrue, that is, forall st, beval st b = beval st BTrue. In particular this means that beval st b = true, but this is a contradiction since E_IfFalse requires that beval st b = false. Thus, the final rule could not have been E_IfFalse.

  * <- We must show that for all st and st', that if c1 / st \\ st' then IFB b THEN c1 ELSE c2 FI / st \\ st'.

  Since b is equivalent to BTrue, we also know that beval st b = beval st BTrue = true.
  Togather with the assumption that c1 / st \\ st' we can apply E_IfTrue to derive that IFB b THEN c1 ELSE c2 FI / st \\ st'.
  *)

Theorem IFB_true : forall b c1 c2,
  bequiv b BTrue ->
  cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H; subst; try auto.
    + unfold bequiv in Hb. simpl in Hb. rewrite Hb in H5. inversion H5.
  - apply E_IfTrue; try auto. unfold bequiv in Hb. simpl in Hb. apply Hb.
Qed.

(* Exercise: 2 stars, recommended (IFB false) *)
Theorem IFB_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - unfold bequiv in Hb. simpl in Hb. inversion H; subst; try auto.
    rewrite Hb in H5. inversion H5.
  - apply E_IfFalse; try auto. unfold bequiv in Hb. simpl in Hb. apply Hb.
Qed.

(* Exercise: 3 stars (swap_if_branches) *)
Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2.
  intros st st'; split.
  - (* -> *) intros E. inversion E; subst.
    + induction b;
      try (apply E_IfFalse; auto);
      try (simpl in *; rewrite <- negb_involutive; apply f_equal; assumption).
    + induction b;
      try (apply E_IfTrue; auto);
      try (simpl in *; rewrite <- negb_involutive; apply f_equal; assumption).
  - (* <- *) intros E. inversion E; subst.
    + induction b;
      try (apply E_IfFalse; auto);
      try (simpl in *; rewrite negb_true_iff in H4; assumption).
    + induction b;
      try (apply E_IfTrue; auto);
      try (simpl in *; rewrite negb_false_iff in H4; assumption).
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv (WHILE b DO c END) SKIP.
Proof.
  intros b c Hb.
  intros st st'.
  split; intros H; unfold bequiv in Hb; simpl in Hb.
  - inversion H; subst.
    + apply E_Skip.
    + rewrite Hb in H2. inversion H2.
  - inversion H; subst. apply E_WhileFalse. apply Hb.
Qed.
















































