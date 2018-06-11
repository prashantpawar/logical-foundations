Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.
Require Export Logic.
Require Export Lists.
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

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a.
  - simpl. apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.

Theorem le_plus_r : forall a b,
  b <= a + b.
Proof.
  intros.
  induction a.
  - simpl. apply le_n.
  - simpl. apply le_S. apply IHa.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  split.
  - apply le_trans with (S (n1 + n2)).
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply H.
  - apply le_trans with (S (n1 + n2)).
    + apply n_le_m__Sn_le_Sm. apply le_plus_r.
    + apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply le_Sn_le in H.
  apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem n_ble_m__Sn_ble_Sm : forall n m,
  leb n m = true -> leb (S n) (S m) = true.
Proof.
  intros. simpl. apply H. Qed.

Theorem Sn_ble_Sm__n_ble_m : forall n m,
  leb (S n) (S m) = true -> leb n m = true.
Proof.
  intros.
  simpl in H. apply H. Qed.


(* 
  if (S 4) <= 5 then 4 <= 5. YES
  if 4 <= (S 3) then 4 <= 3. NO
  if 4 <= 4 then (S 4) <= 5 NO
  if 4 <= 4 then 4 <= (S 4) YES
  if (S 4) <= (S 5) then 4 <= 5 YES
  if (S 4) <= (S 4) then (S 4) <= 4 NO
  if (S 4) <= (S 4) then 4 <= (S 4) YES
  if 4 <= 5 then (S 4) <= (S 5) YES
  
  if leb 4 (S 3) = true then leb 4 3 = true NO
  if leb (S 3) 4 = true then leb 3 4 = true YES
  if leb 4 4 = true then leb 4 (S 4) = true YES
  if leb (S 4) (S 5) = true then leb 4 5 = true YES
  if leb 4 5 = true then leb (S 4) (S 5) = true YES

  O_le_n : 0 <= n.
  le_n_Sm_le : n <= m -> n <= (S m)
  n_le_m__Sn_le_Sm: n ≤ m → S n ≤ S m.
  Sn_le_Sm__n_le_m: S n ≤ S m → n ≤ m.
*)

Theorem ble_Sn_m_n_m : forall n m,
  leb (S n) m = true ->
  leb n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  - intros n contra. inversion contra.
  - intros n H. induction n.
    + reflexivity.
    + simpl. apply IHm. apply Sn_ble_Sm__n_ble_m in H. apply H.
Qed.

Theorem ble_n_m_n_Sm : forall n m,
  leb n m = true ->
  leb n (S m) = true.
Proof.
  intros.
  apply ble_Sn_m_n_m. simpl. apply H. Qed.

Theorem le_n_Sm_le : forall n m, 
  n <= m -> n <= (S m).
Proof.
  intros.
  apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem le_Sn_m_le : forall n m, 
  (S n) <= m -> n <= m.
Proof.
  intros.
  induction m.
  - inversion H.
  - apply le_S. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros m H. induction m.
    + inversion H.
    + apply n_le_m__Sn_le_Sm. apply IHn. simpl in H. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros.
  induction m.
  - inversion H. reflexivity.
  - inversion H.
    + simpl. symmetry. apply leb_refl.
    + apply ble_n_m_n_Sm. apply IHm. apply H1.
Qed.

Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros. 
  apply leb_correct. 
  apply leb_complete in H. 
  apply leb_complete in H0.
  apply le_trans with m.
  - apply H.
  - apply H0.
Qed.


(* Exercise: 2 stars, optional (leb_iff) *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros n m. split.
  - intros H. apply leb_complete. apply H.
  - intros H. apply leb_correct. apply H.
Qed.

(* Exercise: 3 stars, recommended (R_provability) *)
Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

Lemma c2_inverse : forall m n o,
  R (S m) n (S o) ->
  R m n o.
Proof.
  intros.
  apply c3 in H. apply c4 in H. apply H.
Qed.

Lemma c3_inverse : forall m n o,
  R m (S n) (S o) ->
  R m n o.
Proof.
  intros.
  apply c2 in H. apply c4 in H. apply H.
Qed.

Lemma c4_inverse : forall m n o,
  R m n o ->
  R (S m) (S n) (S (S o)).
Proof.
  intros.
  apply c2 in H. apply c3 in H. apply H.
Qed.

Theorem test_R1 :
  R 1 1 2.
Proof.
  apply c2. apply c3. apply c1.
Qed.

Theorem test_R2 :
  R 2 2 6.
Proof.
  apply c2.
  apply c3.
  apply c2.
  apply c3.
Abort. (* Not Provable *)

(* If we dropped constructor c5 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.

No it wouldn't because proposition c2 and c3 already cover that scenario
*)

(* If we dropped constructor c4 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.

Not it wouldn't because proposition c4 increments m, n and o and the set of the rest of the proposition do not offer any convergence on o.
*)

Lemma R_m_n_O : forall o,
  R 0 0 o ->
  o = 0.
Proof.
Admitted.


(* Exercise: 3 stars, optional (R_fact) *)
Definition fR : nat -> nat -> nat :=
  plus.

Example test_R_fR_equ1:
  R 2 3 5 <-> fR 2 3 = 5.
Proof.
  split.
  - reflexivity.
  - intros. apply c2. apply c3. apply c2. apply c3. apply c3. apply c1.
Qed.

Lemma fR_O_n : forall n,
  fR O n = n.
Proof.
  intros. reflexivity.
Qed.

Lemma fR_n_O : forall n,
  fR n O = n.
Proof. intros. induction n.
  - reflexivity.
  - simpl. apply eq_S. apply IHn.
Qed.

Lemma fR_m_Sn : forall m n,
  fR m (S n) = S(fR m n).
Proof.
  intros.
  induction m.
  - reflexivity.
  - simpl. apply eq_S. apply IHm.
Qed.

Lemma fR_n_m_O : forall m n,
  fR m n = 0 ->
  m = 0 /\ n = 0.
Proof. 
  intros. induction n.
  - split.
    + induction m.
      * reflexivity.
      * inversion H.
    + reflexivity.
  - split.
    + induction m.
      * reflexivity.
      * inversion H.
    + rewrite fR_m_Sn in H. inversion H.
Qed.

Lemma n_m_O_fR : forall m n,
  m = 0 /\ n = 0 ->
  fR m n = 0.
Proof. 
  intros. induction n.
  - destruct H. rewrite H. reflexivity.
  - rewrite fR_m_Sn. inversion H. inversion H1.
Qed.

Theorem R_equiv_fR : forall m n o,
  R m n o <-> fR m n = o. 
Proof.
Abort.

(* Exercise: 4 stars, advanced (subsequence) *)
Inductive subseq {X}: list X -> list X -> Prop :=
  | sc_nil : forall l : list X, subseq [] l
  | sc_eq : forall (x : X) (l1 l2:list X), subseq l1 l2 -> subseq (x :: l1) (x::l2)
  | sc_eatl2 : forall (x : X) (l1 l2:list X), subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_test1 : 
  subseq [1;2;3] [1;2;3].
Proof.
  apply sc_eq. apply sc_eq. apply sc_eq. apply sc_nil.
Qed.


Theorem subseq_test2 :
  subseq [1;2;3] [1;1;1;2;2;3].
Proof.
  apply sc_eq. apply sc_eatl2. apply sc_eatl2. apply sc_eq. apply sc_eatl2. apply sc_eq. apply sc_nil.
Qed.

Theorem subseq_test3 :
  subseq [1;2;3] [1;2;7;3].
Proof.
  apply sc_eq. apply sc_eq. apply sc_eatl2. apply sc_eq. apply sc_nil.
Qed.

Theorem subseq_test4 :
  subseq [1;2;3] [5;6;1;9;9;2;7;3;8].
Proof.
  apply sc_eatl2. apply sc_eatl2. apply sc_eq. 
  apply sc_eatl2. apply sc_eatl2. apply sc_eq.
  apply sc_eatl2. apply sc_eq. apply sc_eatl2. 
  apply sc_nil.
Qed.

Theorem subseq_test5 :
  subseq [1;2;3] [1;2].
Proof.
  apply sc_eq. apply sc_eq.
Abort.

Theorem subseq_test6 :
  subseq [1;2;3] [].
Proof.
Abort.

Theorem subseq_test7 :
  subseq [] [1;2].
Proof.
  apply sc_nil.
Qed.

Theorem subseq_refl {X:Type}: forall l : list X,
  subseq l l.
Proof.
  intros l.
  induction l.
  - apply sc_nil.
  - apply sc_eq. apply IHl.
Qed.

Lemma sc_eatl2_inverse : forall (x : nat) (l1 l2 : list nat),
  subseq l1 l2 ->
  subseq l1 (x :: l2).
Proof.
  intros. apply sc_eatl2. apply H.
Qed.

Theorem subseq_app {X}: forall l1 l2 l3 : list X,
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply sc_nil.
  - simpl. apply sc_eq. apply IHsubseq.
  - simpl. apply sc_eatl2. apply IHsubseq.
Qed.

Theorem subseq_shrink : forall (x : nat) (l1 l2 : list nat),
  subseq (x :: l1) l2 -> subseq l1 l2.
Proof.
  intros.
  generalize dependent x.
  generalize dependent l1.
  induction l2.
  - intros. inversion H.
  - intros. apply sc_eatl2. inversion H.
    + apply H1.
    + apply IHl2 with x0. apply H2.
Qed.

Theorem subseq_trans {X}: forall l1 l2 l3 : list X,
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent l1.
  induction H2.
  - intros. inversion H1. apply sc_nil.
  - intros. inversion H1.
    + intros. apply sc_nil.
    + apply sc_eq. apply IHsubseq. apply H3.
    + rewrite <- H0. apply sc_eatl2. apply IHsubseq. rewrite H0. apply H3.
  - intros. apply IHsubseq in H1. apply sc_eatl2. apply H1.
Qed.

Theorem subseq_nil {X}: forall l : list X,
  subseq l [] -> l = [].
Proof.
  intros.
  induction l.
  - reflexivity.
  - inversion H.
Qed.

(* Exercise: 2 stars, optional (R_provability2) *)

Inductive R' : nat -> list nat -> Prop :=
  | c'1 : R' 0 []
  | c'2 : forall n l, R' n l -> R' (S n) (n :: l)
  | c'3 : forall n l, R' (S n) l -> R' n l.

Example test_R'1 : R' 2 [1;0].
Proof.
  apply c'2. apply c'2. apply c'1.
Qed.

Example test_R'2 : R' 1 [1;2;1;0].
Proof.
  apply c'3. apply c'2. 
  apply c'3. apply c'3. apply c'2.
  apply c'2.
  apply c'2.
  apply c'1.
Qed.

Example test_R'3 : R' 6 [3;2;1;0].
Proof.
  apply c'3.
Abort.


(* Case Study: Regular Experssions *)
Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char     : T -> reg_exp
| App      : reg_exp -> reg_exp -> reg_exp
| Union    : reg_exp -> reg_exp -> reg_exp
| Star     : reg_exp -> reg_exp.

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty  : exp_match [] EmptyStr
| MChar   : forall x, exp_match [x] (Char x)
| MApp    : forall s1 re1 s2 re2, 
              exp_match s1 re1 ->
              exp_match s2 re2 ->
              exp_match (s1 ++ s2) (App re1 re2)
| MUnionL  : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR  : forall s1 re1 re2,
              exp_match s1 re2 ->
              exp_match s1 (Union re1 re2)
| MStar0  : forall re, exp_match [] (Star re)
| MStarApp: forall s1 s2 re,
              exp_match s1 re ->
              exp_match s2 (Star re) ->
              exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex12 : [1; 2] =~ App (Char 1) (Char 2).
Proof. 
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros contra.
  inversion contra.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
         s =~ re ->
         s =~ Star re.
Proof.
  intros.
  rewrite <- app_nil_r with (l:=s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(* Exercise: 3 stars (exp_match ex1) *)
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not.
  intros T s contra.
  inversion contra.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  - apply MUnionL. apply H1.
  - apply MUnionR. apply H2.
Qed.

Lemma MApp' : forall T (s1 s2 : list T) (re1 re2 : @reg_exp T),
  s1 =~ re1 /\ s2 =~ re2 ->
  s1 ++ s2 =~ App re1 re2.
Proof.
  intros T s1 s2 re1 re2 [H1 H2].
  apply MApp.
  - apply H1.
  - apply H2.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl. simpl in H. apply MStar0.
  - simpl. apply MStarApp.
    + simpl in H. apply H. left. reflexivity.
    + simpl in H. apply IHss. intros. apply H. right. apply H0.
Qed.

Lemma app_plus : forall T x (l : list T),
  x :: l = [x] ++ l.
Proof.
  reflexivity.
Qed.

Lemma reg_exp_of_list_refl : forall T (s : list T),
  s =~ reg_exp_of_list s.
Proof.
  intros. induction s.
  - simpl. apply MEmpty.
  - simpl. rewrite app_plus. apply MApp.
    + apply MChar.
    + apply IHs.
Qed.

(* Exercise: 4 stars, optional (reg_exp_of_list_spec) *)

Lemma reg_exp_of_list_empty : forall T (s : list T),
  s = [] ->
  [] =~ reg_exp_of_list s.
Proof.
  intros. induction s.
  - simpl. apply MEmpty.
  - simpl. inversion H.
Qed.

Lemma reg_exp_of_list_basic : forall T (s1 s2 : list T),
  s1 = s2 ->
  s1 =~ reg_exp_of_list s2.
Proof.
  intros.
  generalize dependent s1.
  induction s2.
   - intros. simpl. rewrite H. apply MEmpty.
   - intros. simpl. rewrite H. rewrite app_plus. apply (MApp [x] _ _).
      + apply MChar.
      + apply reg_exp_of_list_refl.
Qed.

Lemma reg_exp_of_list_basic_inv : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 ->
  s1 = s2.
Proof.
  intros.
  generalize dependent s1.
  induction s2 as [| x2].
  - intros. simpl in H. inversion H. reflexivity.
  - intros. inversion H. inversion H3. apply f_equal. apply IHs2. apply H4.
Qed.


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  - apply reg_exp_of_list_basic_inv.
  - apply reg_exp_of_list_basic.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.
  


Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - apply Hin.
  - apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - simpl. rewrite In_app_iff. left. apply (IH Hin).
  - simpl. rewrite In_app_iff. right. apply (IH Hin).
  - destruct Hin.
  - simpl. apply In_app_iff in Hin. 
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.

(* Exercise: 4 stars (re_not_empty) *)
Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star _ => true
  end.

(* Compute (re_not_empty (Star (EmptySet))). *)
Compute (re_not_empty (Char [1;2;3;4])).
Compute (re_not_empty (App (Char 1) (EmptySet))).

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  { intros H. induction re.
    - (* EmptySet *) inversion H. inversion H0.
    - (* EmptyStr *) reflexivity.
    - (* Char _ *) reflexivity.
    - (* App _ _ *) simpl. rewrite andb_true_iff. split.
      + (* re1 *) apply IHre1. inversion H. inversion H0. exists s1. apply H4.
      + (* re2 *) apply IHre2. inversion H. inversion H0. exists s2. apply H5.
    - (* Union _ _ *) simpl. apply orb_true_iff. inversion H. inversion H0.
      + left. apply IHre1. exists x. apply H3.
      + right. apply IHre2. exists x. apply H3.
    - (* Star *) reflexivity. }
    { induction re.
      - (* EmptySet *) intros. inversion H.
      - (* EmptyStr *) exists []. apply MEmpty.
      - (* Char _ *) exists [t]. apply MChar.
      - (* App _ _ *) intros. inversion H. apply andb_true_iff in H1. 
        destruct H1. apply IHre1 in H0. apply IHre2 in H1. 
        inversion H0. inversion H1. exists (x ++ x0). apply MApp.
        + apply H2.
        + apply H3.
      - (* Union _ _ *) intros. inversion H. apply orb_true_iff in H1.
        destruct H1.
        + apply IHre1 in H0. inversion H0. exists x. apply MUnionL. apply H1.
        + apply IHre2 in H0. inversion H0. exists x. apply MUnionR. apply H1.
      - (* Star _ *) intros. exists []. apply MStar0. }
Qed.


(* The remember tactic *)

Lemma star_app': forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  induction re'.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H.
  - intros. inversion H. inversion H0. 
    + simpl. apply H1.
    + subst. apply IHre'.
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1.
  - (* MEmpty *) inversion Heqre'.
  - (* MChar *) inversion Heqre'.
  - (* MApp *) inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *) intros. simpl. apply H.
  - (* MStarApp *) inversion Heqre'. intros. rewrite H0 in IHexp_match1. rewrite H0 in IHexp_match2. rewrite <- app_assoc. apply MStarApp.
    + rewrite H0 in H1_. apply H1_.
    + apply IHexp_match2.
      * reflexivity.
      * apply H.
Qed.


Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  generalize dependent re.
  induction H.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. exists []. split.
    + reflexivity.
    + intros. inversion H.
  - intros. remember (s1 ++ s2) as ss. Admitted.


(*
  - intros. induction (s1 ++ s2).
    + exists []. split.
      * reflexivity.
      * simpl. intros. inversion H1.
    + exists [x :: l]. split.
      * simpl. rewrite app_nil_r. reflexivity.
      * simpl. destruct IHl. destruct H1. intros. apply H2. simpl in H3. destruct H3.
        { -   

  
  
  
  intros. remember (s1 ++ s2) as ss. induction re.
    + intros. inversion Heqre'. exists [s1 ++ s2]. split.
      * simpl. symmetry. apply app_nil_r.
      * rewrite H2. 



    exists [s1 ++ s2]. split.
    + simpl. symmetry. apply app_nil_r.
    + 
      intros. simpl in H1. destruct H1.
      * 

*)
(* 
  intros T s re.
  remember (Star re) as re'.
  generalize dependent re'.
  induction re.
  - intros. induction s. 
    + exists []. split.
      * reflexivity.
      * intros. inversion H0.
    + exists ([x :: s]). split.
      * simpl. rewrite app_nil_r. reflexivity.
      * intros. simpl in H0. destruct H0.
        { - inversion H0.
    
    exists [s]. split.
    + simpl. symmetry. apply app_nil_r.
    + intros. 
    inversion H.
    + exists [s]. simpl. split.
      * rewrite app_nil_r. apply H0.
      * intros. induction Heqre'. apply MEmpty.




  intros T s re.
  remember (Star re) as re'.
  generalize dependent re.
  induction re'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'. 
    exists [s]. split.
    + simpl. symmetry. apply app_nil_r.
    + intros. inversion H.
      * rewrite <- H2 in H. simpl in H0. 
      intros. simpl in H0. destruct H0.
      * 
        rewrite Heqre' in H. apply MStar0. in H.








  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. exists [s]. split.
    + simpl. rewrite app_nil_r. reflexivity.
    + apply IHre'. intros. simpl in H0. destruct H0.
      * 


*)
(* Almost succeeded
  intros T s re H.
  remember (Star re) as re'.
  generalize dependent re.
  induction H.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. exists []. split.
    + reflexivity.
    + intros. inversion H.
  - intros. exists [s1 ++ s2]. split.
    + simpl. symmetry. apply app_nil_r.
    + simpl.
      inversion Heqre'.
      intros. simpl in H1. destruct H1.
      * 
      apply IHexp_match2. rewrite <- H1.



  - simpl. rewrite app_nil_r. reflexivity.
  - apply MStar1 in H. induction H. 
    + intros. simpl in H. inversion H
    + rewrite <- H0. Search Star. 
  
  
  
  
  
  induction re'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'. rewrite H1 in IHre'. apply IHre'.
      { Search Star. induction re.
        - inversion H.
        Search MStar'. inversion Heqre'.
*)

(* Exercise: 5 stars, advanced (pumping) *)
Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus : forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. apply app_assoc.
Qed.

Lemma pumping: forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Import Coq.omega.Omega.
Proof.
  intros T re s Hmatch.  
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *) simpl. omega.
  - (* MChar *) simpl. omega.
  - (* MApp *) simpl. intros. exists s1. exists s2. exists []. simpl. split.
    + rewrite app_nil_r. reflexivity.
    + split.
Abort.

End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros. apply H. reflexivity.
  - simpl. destruct (beq_nat n m) eqn:H.
    + intros. left. apply beq_nat_true_iff in H. rewrite H. reflexivity.
    + intros. right. apply IHl'. apply H0.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~P -> reflect P false.

Theorem iff_reflect : forall P b, 
  (P <-> b = true) -> reflect P b.
Proof.
  intros. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. unfold not. intros. inversion H0.
Qed.

(* Exercise: 2 stars, recommended (reflect_iff) *)
Theorem reflect_iff : forall P b,
  reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct b.
  - split.
    + intros. reflexivity.
    + intros. inversion H. apply H1.
  - split.
    + intros. inversion H. exfalso. apply H1. apply H0.
    + intros. inversion H0.
Qed.

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.


Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_natP n m) as [H | H].
    + intros _. rewrite H. left. reflexivity.
    + intros. unfold not in H. right. apply IHl'. apply H0.
Qed.

(* Exercise: 3 stars, recommended (beq_natP_practice) *)
Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros. induction l as [|m l' IHl'].
  - simpl. unfold not. intros contra. apply contra.
  - simpl. unfold not. intros. simpl in H. destruct (beq_natP n m) as [H1 | H1].
    + inversion H.
    + simpl in H. unfold not in H1. destruct H0.
      * symmetry in H0. apply H1 in H0. apply H0.
      * apply IHl' in H0.
        { - apply H0. }
        { - apply H. }
Qed.

(* Additional Exercises *)
(*Exercise: 3 stars, recommended (nostutter_defn) *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | NSEmpty : nostutter []
  | NSSingleEl : forall n : X, nostutter [n]
  | NSRepeated : forall (m n : X) (xs : list X), 
      m <> n -> nostutter (n :: xs) -> nostutter (m :: n :: xs).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply beq_nat_false_iff; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  repeat constructor.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  repeat constructor; apply beq_nat_false; auto.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _|- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto.
Qed.

(* Exercise: 4 stars, advanced (filter_challenge) *)
Inductive inordermerge {X:Type} : list X -> list X -> list X -> Prop :=
  | IOMEmpty : inordermerge [] [] []
  | IOMMatchesL1 : forall (n : X) (l1 l2 l : list X),
      inordermerge l1 l2 l -> inordermerge (n :: l1) l2 (n :: l)
  | IOMMatchesL2 : forall (n : X) (l1 l2 l : list X),
      inordermerge l1 l2 l -> inordermerge l1 (n :: l2) (n :: l).

Example test_inordermerge_1 : inordermerge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  repeat constructor.
Qed.

Example test_inordermerge_2 : inordermerge [1;6;2] [] [1;6;2].
Proof.
  repeat constructor.
Qed.

Example test_inordermerge_3 : not (inordermerge [1;2;3] [4;5;6] [1;4;6]).
Proof.
  intro.
  inversion H. clear H. subst.
  inversion H3. clear H3. subst.
  inversion H1.
Qed.

Lemma head_same {X:Type}: forall (x:X) (l1 l2 : list X),
  l1 = l2 ->
  x :: l1 = x :: l2.
Proof.
  intros. simpl. inversion H. reflexivity.
Qed.


(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)
Inductive all {X:Type} : (X -> Prop) -> list X -> Prop :=
  | all_nil : forall (P:X -> Prop), all P []
  | all_match : forall (x:X) (l:list X) (P:X -> Prop), P x -> all P l -> all P (x::l).

Example test_all_1 : all ev [0;2;4].
Proof.
  repeat constructor.
Qed.

Example test_all_2: ~(all ev [2;3;4;5]).
Proof.
  intro.
  inversion H. clear H. subst.
  inversion H4. clear H4. subst.
  inversion H2. inversion H0.
Qed.


(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)
Fixpoint forallb X (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => test x && forallb X test l'
  end.


Lemma all_app {X:Type}: forall (x:X) (l:list X) (P: X -> Prop),
  all P (x :: l) ->
  P x /\ all P l.
Proof.
  intros. split.
  - inversion H. apply H3.
  - inversion H. apply H4.
Qed.


(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.
    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)
Theorem all_forallb {X:Type} :
  forall (test : X -> bool) (P: X -> Prop) (l : list X),
  (forall n, test n = true /\ P n) ->
  all P l ->
  forallb X test l = true.
Proof.
  intros.
  induction H0.
  - reflexivity.
  - simpl. apply andb_true_iff. split.
    + destruct H with (n:=x). apply H2.
    + apply IHall. apply H.
Qed.

Theorem filter_challenge {X:Type} :
  forall (l l1 l2: list X) (test:X->bool),
  (forall x, In x l1 -> test x = true) ->
  (forall x, In x l2 -> test x = false) ->
  inordermerge l1 l2 l ->
  filter test l = l1.
Proof.
  intros l l1 l2 test Hl1 Hl2 H.
  induction H.
  - reflexivity.
  - simpl. assert (test n = true) as C.
    + apply Hl1. simpl. left. reflexivity.
    + rewrite C. apply head_same. apply IHinordermerge.
      * intros. apply Hl1. simpl. right. trivial.
      * intros. apply Hl2. trivial.
  - simpl. assert (test n = false) as C.
    + apply Hl2. simpl. left. reflexivity.
    + rewrite C. apply IHinordermerge.
      * apply Hl1.
      * intros. apply Hl2. simpl. right. apply H0.
Qed.

Theorem subseq_pad_l2 : forall (x : nat) (l1 l2 : list nat),
  subseq l1 l2 -> subseq l1 (x :: l2).
Proof.
  intros.
  generalize dependent x.
  generalize dependent l2.
  induction l1.
  - intros. apply sc_nil.
  - intros. simpl in *. apply sc_eatl2. apply H.
Qed.


(* Exercise: 5 stars, advanced (filter_challenge_2) *)
Theorem filter_challenge_2 {X} :
  forall (ls l : list X) (test:X->bool),
  subseq ls l ->
  (forall n, In n ls -> test n = true) ->
  length ls <= length (filter test l).
Proof.
  intros ls l test Hsubseq G.
  induction Hsubseq.
  - apply O_le_n.
  - simpl. assert (test x = true) as C.
    + apply G. simpl. left. reflexivity.
    + rewrite C. simpl. apply n_le_m__Sn_le_Sm. apply IHHsubseq.
      intros. apply G. simpl. right. apply H.
  - simpl. destruct (test x) eqn:C.
    + simpl. apply le_S. apply IHHsubseq. intros. apply G. apply H.
    + apply IHHsubseq. intros. apply G. apply H.
Qed.


(* Exercise: 4 stars, optional (palindromes) *)

Inductive matchlast {X} : X -> list X -> list X -> Prop :=
  | match_same : forall (x:X), matchlast x [x] []
  | match_tail : forall (x y:X) (l m:list X), 
      matchlast x l m -> matchlast x (y :: l) (y :: m).

Inductive pal {X} : list X -> Prop :=
  | pal_nil : pal []
  | pal_single : forall x, pal [x]
  | pal_match : forall (x:X) (l m:list X),
      pal l -> matchlast x m l -> pal (x :: m).

Inductive pal2 {X} : list X -> Prop :=
  | c : forall l, l = rev l -> pal2 l.

Lemma matchx_last {X} : forall (x:X) (m:list X),
  matchlast x (m ++ [x]) m.
Proof.
  induction m.
  - simpl. apply match_same.
  - simpl. apply match_tail. apply IHm.
Qed.

Theorem pal_app_rev {X}: forall (l:list X),
  pal (l ++ rev l).
Proof.
  induction l.
  - simpl. apply pal_nil.
  - simpl. rewrite app_plus. apply pal_match with (l0:=(l ++ rev l)).
    + apply IHl.
    + rewrite app_assoc. inversion IHl.
      * simpl. apply match_same.
      * apply match_tail. apply match_same.
      * simpl. apply match_tail. apply matchx_last.
Qed.

Lemma rev_l {X}: forall (x:X) (l:list X),
  l = rev l ->
  x :: l = rev l ++ [x].
Proof.
  intros.
  rewrite app_plus. symmetry. rewrite <- rev_involutive. 
  rewrite rev_app_distr. rewrite <- H. simpl.
  symmetry. rewrite <- rev_involutive.
Abort.

Theorem pal2_rev {X}: forall (l:list X),
  pal2 l -> l = rev l.
Proof.
  induction l.
  - intros. reflexivity.
  - intros. simpl. rewrite app_plus. inversion H. simpl in H0.
    rewrite <- H0. reflexivity.
Qed.

Lemma tail_same {X:Type}: forall (x:X) (l1 l2 : list X),
  l1 = l2 ->
  l1 ++ [x] = l2 ++ [x].
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem pal2_app_rev {X}: forall (l:list X),
  pal2 (l ++ rev l).
Proof.
  intros. induction l.
  - simpl. apply c. reflexivity.
  - simpl. rewrite app_plus. apply c.
    inversion IHl. rewrite rev_app_distr.
    rewrite rev_app_distr. rewrite rev_app_distr.
    rewrite rev_involutive. simpl. rewrite app_plus. symmetry.
    rewrite app_plus. rewrite <- app_assoc. reflexivity.
Qed.


Lemma pal_prefix {X} : forall (x:X) (l1 l2:list X),
  pal ([x] ++ l1) -> l1 = l2 ++ [x].
Proof.
  Admitted.


Theorem pal_rev {X}: forall (l:list X),
  pal l -> l = rev l.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - reflexivity.
  - inversion H1.
    + reflexivity.
    + subst. simpl in *.
Abort.

Theorem test_pal_1 : pal [1].
Proof.
  apply pal_single.
Qed.

Hint Resolve pal_nil pal_single pal_match match_same match_tail.

Theorem test_pal_2 : pal [1;2;1].
Proof.
  apply pal_match with (l:=[2]).
  - apply pal_single.
  - apply match_tail. apply match_same.
Qed.

Theorem test_pal_3 : pal [1;2;3;2;1].
Proof.
  apply pal_match with (l:=[2;3;2]).
  - apply pal_match with (l:=[3]).
    + apply pal_single.
    + apply match_tail. apply match_same.
  - apply match_tail. apply match_tail. apply match_tail. apply match_same.
Qed.

Theorem test_pal_4 : pal [1;2;3;3;2;1].
Proof.
  apply pal_match with (l:=[2;3;3;2]).
  - apply pal_match with (l:=[3;3]).
    + apply pal_match with (l:=[]).
      * apply pal_nil.
      * apply match_same.
    + apply match_tail. apply match_tail. apply match_same.
  - apply match_tail. apply match_tail. apply match_tail. apply match_tail. apply match_same.
Qed.

Lemma rev_eq_pal_length: forall (X: Type) (n: nat) (l: list X),
  length l <= n -> l = rev l -> pal l.
Proof.
  intros.
  induction n.
  - inversion H.
    assert (G: l = []).
    { - induction l.
        + reflexivity.
        + inversion H2. }
    rewrite G. apply pal_nil.
  - induction l.
    + apply pal_nil. 
    + simpl in *. inversion H. 
Abort.

(* Exercise: 5 stars, optional (palindrome_converse) *)
Theorem palindrome_converse {X} : forall (l:list X),
  l = rev l -> pal l.
Proof.
  intros.
Abort.

(* Exercise: 4 stars, advanced, optional (NoDup) *)
(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

Inductive NoDup {X}: list X -> Prop :=
  | NoDup_nil : NoDup []
  | NoDup_element : forall (x:X) (l:list X), NoDup l -> ~ In x l -> NoDup (x :: l).

Example tests_nodup_1 : NoDup [1;2;3;4].
Proof.
  apply NoDup_element.
  - apply NoDup_element.
    + apply NoDup_element.
      * apply NoDup_element.
        { - apply NoDup_nil. }
        { - auto. }
      * simpl. unfold not. intros. destruct H. inversion H. apply H.
    + simpl. unfold not. intros. destruct H.
      * inversion H.
      * destruct H.
        { - inversion H. }
        { - apply H. }
  - unfold not. intros. destruct H.
    + inversion H.
    + destruct H.
      * inversion H.
      * simpl in H. destruct H.
        { - inversion H. }
        { - apply H. }
Qed.

Example tests_nodup_2 : NoDup [1;2;1].
Proof.
  apply NoDup_element.
  - apply NoDup_element.
    + apply NoDup_element.
      * apply NoDup_nil.
      * simpl. auto.
    + unfold not. intros. destruct H. inversion H. apply H.
 - unfold not. intros. destruct H. inversion H. Abort. 


Fixpoint disjoint {X} (l1 l2: list X) : Prop :=
  ~ exists x, In x l1 /\ In x l2.


Lemma disjoint_empty {X:Type} : forall (l:list X), 
  disjoint l [].
Proof.
  intros. induction l.
  - simpl. unfold not. intros. destruct H. destruct H. apply H.
  - simpl. unfold not. intros. destruct H. destruct H. apply H0.
Qed.

Lemma disjoint_refl_false {X} : forall (l:list X),
  l <> [] -> 
  ~ disjoint l l.
Proof.
  intros.
  induction l.
  - simpl. unfold not. intros. apply H. reflexivity. 
  - simpl. unfold not. intros. apply H0. exists x. split.
    + left. reflexivity.
    + left. reflexivity.
Qed.

Lemma In_empty {X:Type} : forall x:X,
  ~ In x [].
Proof.
  intros. unfold not. intros.
  inversion H.
Qed.


Theorem NoDup_disjoint_app {X} : forall l1 l2 : list X,
  disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  intros. induction l2.
  - induction l1.
    + simpl. apply NoDup_nil.
    + simpl. rewrite app_nil_r in *. apply NoDup_element.
      * apply IHl1. apply disjoint_empty.
      * unfold not. intros. induction IHl1. 
        { - inversion H0. }
        { - apply IHn.
            + apply disjoint_empty.
            + unfold not in H1.
      exists x. split.
        { - simpl. left. reflexivity. }
        { - simpl. 

  intros. induction l1.
  - induction l2.
    + apply NoDup_nil.
    + apply NoDup_element.
      * simpl in *. apply IHl2. unfold not in *. intros. destruct H0. destruct H0. apply H0.
      * admit.
  - induction l2.
    + simpl. rewrite app_nil_r in *. apply NoDup_element.
      * apply IHl1. apply disjoint_empty.
      * destruct IHl1.
        { - apply disjoint_empty. }
        { - unfold not. intros. inversion H0. } 
        { - simpl. unfold not in *. intros. apply H0. destruct H1.
            + rewrite H1. admit.
            + 








  intros. 
  induction (l1 ++ l2).
  - apply NoDup_nil.
  - apply NoDup_element.
    + apply IHl.
    + unfold not. intros. induction l1.
      * 









  intros. induction l2.
  - induction l1.
    + simpl. apply NoDup_nil.
    + simpl. rewrite app_nil_r in *. apply NoDup_element.
      * apply IHl1. apply disjoint_empty.
      * unfold not. intros. induction H. exists x. split.
        { - simpl. left. reflexivity. }
        { - 
        
        
        
        
        
        simpl. rewrite app_nil_r in IHl1. destruct IHl1.
            + apply disjoint_empty.
            + simpl in H0. apply H0.
            + unfold not in H. apply H. inversion H0. 
              * inversion n.
                { - apply In_empty.














                 rewrite H1 in H0. rewrite app_plus in H0. Search In. apply In_app_iff in H0. destruct H0.
                { - apply H. rewrite H1.


              Search In. inversion H0. apply H. rewrite <- H1 in H0. inversion H0.
                { - rewrite <- H1 in *. inversion H0. rewrite H2. apply In_empty.


            destruct H. simpl in H0. destruct H0.
              * rewrite H. apply 







  intros. induction l1.
  - simpl in *. induction l2.
    + apply NoDup_nil.
    + apply NoDup_element.
      * apply IHl2. unfold not in *. intros. destruct H0. destruct H0. apply H0.
      * destruct H. exists x. split.
        { - 
        unfold not in *. intros. apply H. exists x. split.
        { - 



  unfold not in H. destruct H. exists 
Qed.






































