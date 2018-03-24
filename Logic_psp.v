Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.

Check 3 = 3.

Check forall n m : nat, n + m = m + n.

Check 2 = 2.

Check forall n : nat, n = 2.

Check 3 = 4.


Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof.
  reflexivity.
Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof.
  reflexivity.
Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.

Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop,
  A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 2 stars (and_exercise) *)
Example and_exercise_firsttry :
  forall n m : nat,
  n + m = 0 ->
  n = 0 /\ m = 0.
Proof.
  intros n m H.
  induction n, m.
  - auto.
  - auto.
  - split.
    + simpl in H. rewrite <- plus_n_O in H. apply H.
    + auto.
  - inversion H.
Qed.

Example and_exercise :
  forall n m : nat,
  n + m = 0 ->
  n = 0 /\ m = 0.
Proof.
  intros n m H.
  induction n.
  - auto.
  - inversion H.
Qed.


Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 ->
  n + m = 0.
Proof.
  intros.
  destruct H as [Hn Hm].
  rewrite Hn. apply Hm.
Qed.

Lemma and_example2' : forall n m : nat,
  n = 0 ->
  m = 0 ->
  n + m = 0.
Proof.
  intros.
  rewrite H. apply H0.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 ->
  n * m = 0.
Proof.
  intros.
  assert (H' : n = 0 /\ m = 0).
  { induction n.
    - auto.
    - inversion H.
  }
  destruct H' as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.


Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.


(* Exercise: 1 star, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

(* Exercise: 2 stars (and_assoc) *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check and.


Lemma or_example : forall n m : nat,
  n = 0 \/ m = 0 ->
  n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on 
    n = 0 \/ m = 0 *)
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.


Lemma or_intro : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros.
  induction n.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quadlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(* Exercise: 2 stars, optional (not_implies_our_not) *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  destruct H.



























