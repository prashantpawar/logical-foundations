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
   intros c st st'.
   split.
   - (* -> *) intros. inversion H. inversion H2. auto.
   - (* <- *) intros. apply E_Seq with st; auto.
    + apply E_Skip.
Qed.

(* Exercise: 2 stars (skip_right) *)
Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  intros c st st'.
  split.
  - (* -> *) intros. inversion H; subst. inversion H5; subst. auto.
  - (* <- *) intros. apply E_Seq with st'; auto.
    + apply E_Skip.
Qed.

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2 st st'.
  split.
  - (* -> *) intros. inversion H; subst; auto. inversion H5.
  - (* <- *) intros. apply E_IfTrue; auto.
Qed.

Theorem IFB_true: forall b c1 c2,
  bequiv b BTrue ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 E st st'.
  split; intros.
  - (* -> *) inversion H; subst; auto. unfold bequiv in E.
    rewrite E in H5. simpl in H5; inversion H5.
  - (* <- *) apply E_IfTrue; auto. apply E.
Qed.

(* Exercise: 2 stars, recommended (IFB_false) *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros b c1 c2 E st st'.
  split; intros.
  - (* -> *) inversion H; subst; auto.
    + unfold bequiv in E. rewrite E in H5. inversion H5.
  - (* <- *) apply E_IfFalse; auto. apply E.
Qed.

(* Exercise: 3 stars (swap_if_branches) *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'.
  split; intros.
  - (* -> *) inversion H; subst.
    + apply E_IfFalse; auto. simpl.
      apply negb_false_iff. auto.
    + apply E_IfTrue; auto. simpl.
      apply negb_true_iff. auto.
  - (* <- *) inversion H; subst.
    + simpl in H5. apply negb_true_iff in H5. apply E_IfFalse; auto.
    + simpl in H5. apply negb_false_iff in H5. apply E_IfTrue; auto.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c E st st'.
  split; intros.
  - (* -> *) unfold bequiv in E. inversion H; subst.
    + apply E_Skip.
    + rewrite E in H2. inversion H2.
  - (* <- *) unfold bequiv in E. inversion H; subst.
    apply E_WhileFalse. apply E.
Qed.

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  intros b c st st' E.
  unfold not.
  intros.
  inversion H; subst.
  - unfold bequiv in E. rewrite E in H4. inversion H4.
  - induction H; subst.
  unfold bequiv in E. inversion H3.
  
  
  
  
  
  
  inversion H6; subst. rewrite E in H7.
    simpl in H7. inversion H7.
    + 

























  induction b; unfold bequiv in E.
  - inversion H; subst;
     try (inversion H4).
    + inversion H4.
    + inversion H4.
  - inversion H; subst.
    + rewrite E in H4. inversion H4.
    + inversion H2.
  - simpl in E. 




  inversion H; subst.
  - rewrite E in H4. inversion H4.
  - induction c

























