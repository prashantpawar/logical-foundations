Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.
Require Export Logic.
Require Coq.omega.Omega.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).


Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* Exercise: 1 star (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. rewrite double_plus. induction n.
  - simpl. apply ev_0.
  - simpl. rewrite <- plus_n_Sm. apply ev_SS. apply IHn.
Qed.


(* Using Evidence in Proofs *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E.
  - simpl. apply ev_0.
  - simpl. apply E.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.


(* Exercise: 1 star (SSSSev_even) *)
Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  inversion E'. apply H1.
Qed.

(* Exercise: 1 star (even5_nonsense) *)
Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H.
  inversion H1. inversion H3.
Qed.

Lemma ev_even_firsttry : forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  inversion E as [| p E'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E' *)
    assert (I : (exists r, p = double r) ->
                (exists k, S (S p) = double k)). 
    { intros [r Hr]. rewrite Hr. exists (S r). reflexivity. }
    apply I. 
Abort.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [| n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). simpl. reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros. unfold iff. split.
  - apply ev_even.
  - intros [k' Hk']. rewrite Hk'. apply ev_double.
Qed.

(* Exercise: 2 stars (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em. induction En.
  - simpl. apply Em.
  - simpl. apply ev_SS. apply IHEn.
Qed.

(* Exercise: 4 stars, advanced, optional (ev' ev) *)
Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_1 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros. split.
  - intros E. induction E.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IHE1.
      * apply IHE2.
  - intros E. induction E.
    + apply ev'_0.
    + assert (I : forall n, S (S n) = n + 2).
      { - intros. induction n0.
          + reflexivity.
          + simpl. rewrite IHn0. reflexivity. }
      rewrite I. apply ev'_sum.
        * apply IHE.
        * apply ev'_1.
Qed.

(* Exercise: 3 stars, advanced, recommended (ev_ev__ev) *)

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Enm En. induction En.
  - simpl in Enm. apply Enm.
  - simpl in Enm. apply IHEn. apply evSS_ev in Enm. apply Enm.
Qed.


(* Exercise: 3 stars, optional (ev_plus_plus) *)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros. apply ev_sum with (n + m) (n + p) in H.
  - rewrite plus_swap in H. rewrite <- plus_assoc in H.
    rewrite plus_assoc with n n (m + p) in H.
    apply ev_ev__ev with (n + n) (m + p) in H.
    + apply H.
    + rewrite <- double_plus. apply ev_double.
  - apply H0.
Qed.


Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof. apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.

End Playground.


Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).


(* Exercise: 3 stars, optional (le_exercises) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hmo.
  induction Hmo.
  - apply Hmn.
  - apply le_S. apply IHHmo.
Qed.


Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem le_Sn_le : forall n m, 
  S n <= m -> n <= m.
Proof.
  intros.
  apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - apply le_trans with (S n).
    + apply le_S. apply le_n.
    + apply H1.
Qed.

Theorem le_plus_1 : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a.
  - simpl. apply le_0_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.






































