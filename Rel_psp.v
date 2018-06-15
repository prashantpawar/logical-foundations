Set Warnings "-notation-overridden,-parsing".
Require Export IndProp.

(* Relations *)
Definition relation (X: Type) := X -> X -> Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

(* Basic Properties *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X,
    R x y1 -> R x y2 -> y1 = y2.

Print next_nat.

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros.
  inversion H.
  inversion H0.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  not (partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros Hc.
  assert (0 = 1) as Nonsense. {
    - apply Hc with (x := 0).
      + reflexivity.
      + apply le_S. reflexivity. }
  inversion Nonsense.
Qed.

(* Exercise: 2 stars, optional (total_relation_not_partial) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  | total_re : forall n m : nat, total_relation n m.

Theorem total_relation_not_partial :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function.
  intros Hc.
  assert (0 = 1) as Nonsense. {
    - apply Hc with (x := 0).
      + apply total_re.
      + apply total_re. }
  inversion Nonsense.
Qed.

(* Exercise: 2 stars, optional (empty_relation_partial) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=.

Theorem empty_relation_partial :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H0 H1.
  inversion H0.
Qed.

(* Reflexive Relations *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intros a.
  reflexivity.
Qed.

(* Transitive Relations *)
Definition transitive {X : Type} (R: relation X) :=
  forall a b c : X, R a b -> R b c -> R a c.

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo.
Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros a b c Hab Hbc.
  apply le_S in Hab.
  apply le_trans with (a:= (S a)) (b := (S b)) (c := c).
  - apply Hab.
  - apply Hbc.
Qed.

(* Exercise: 2 stars, optional (le_trans_hard_way) *)
Theorem le_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S. apply Hnm.
  - apply le_S. apply IHHm'o.
Qed.

(* Exercise: 2 stars, optional (lt_trans'') *)
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o.
  - inversion Hmo.
  - apply le_S in Hnm.
    induction Hmo.
    + apply Hnm.
    + apply le_S. apply IHHmo.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m Hnm.
  apply le_trans with (S n).
  - apply le_S. reflexivity.
  - apply Hnm.
Qed.

(* Exercise: 1 star, optional (le_S_n) *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros.
  apply le_S_n. apply H.
Qed.

(* Exercise: 2 stars, optional (le_Sn_n_inf) *)
(*
Theorem: For every n, not (S n <= n).
Proof.
  Lets begin by performing induction on n.
  1. n = 0, we have to prove that (S 0 <= 0) is False that is (1 <= 0) is false, this is trivial.
  2. For some value of n' this goal holds true for S n'.
  That is (S (S n') <= S n') is false given (S n' <= n') is False.
  We know that if S m <= S n is true then m <= n is true.
  Based on this our goal can be reduced to prove that (S n' <= n') is false. Since this is our hypothesis, this is proven
  *)


(* Exercise: 1 star, optional (le_Sn_n) *)

Theorem le_Sn_n : forall n,
  not (S n <= n).
Proof.
  induction n.
   - unfold not. intros contra. inversion contra.
   - unfold not in *. intros. apply IHn. apply Sn_le_Sm__n_le_m. apply H.
Qed.

(* Symmetric and Antisymmetric Relations *)

Definition symmetric {X:Type} (R: relation X) :=
  forall a b : X, R a b -> R b a.

(* Exercise: 2 stars, optional (le_not_symmetric) *)

Theorem le_not_symmetric :
  not (symmetric le).
Proof.
  unfold symmetric.
  unfold not.
  intros.
  assert (1 <= 0).
  - apply H. apply le_0_n.
  - inversion H0.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* Exercise: 2 stars, optional (le_antisymmetric) *)

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b Hab Hba.
  generalize dependent a.
  induction b.
  - intros. inversion Hab. reflexivity.
  - destruct a.
    + intros. inversion Hba.
    + intros. apply eq_S. apply IHb.
      * apply le_S_n in Hab. apply Hab.
      * apply le_S_n in Hba. apply Hba.
Qed.
































