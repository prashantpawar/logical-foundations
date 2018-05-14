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
Inductive subseq : list nat -> list nat -> Prop :=
  | sc_nil : forall l : list nat, subseq [] l
  | sc_eq : forall (x : nat) (l1 l2:list nat), subseq l1 l2 -> subseq (x :: l1) (x::l2)
  | sc_eatl2 : forall (x : nat) (l1 l2:list nat), subseq l1 l2 -> subseq l1 (x :: l2).

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

Theorem subseq_refl : forall l,
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

Theorem subseq_app : forall l1 l2 l3,
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


(*
Totally Cheated on this one
*)

Theorem subseq_trans : forall l1 l2 l3,
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











































