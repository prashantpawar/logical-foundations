Set Warnings "-notation-overridden,-parsing".
Require Import Coq.omega.Omega.
Require Import Maps.
Require Import Imp.

Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *) reflexivity.
  - (* b evaluates to true (contradiction) *) rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0).
    { (* Proof of assertion *) apply IHE1_1. assumption. }
    subst st'0. apply IHE1_2. assumption. Qed.


(* The auto tactic *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2: forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof.
  auto.
Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, auto does nothing *)
  auto.
  (* Optional argument says how deep to search (default is 5) *)
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> (n = m).
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto.
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7': forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0. auto.
  - (* E_IfTrue *) 
    + (* b evaluates to false (contradiction) *) rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *) rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *) rewrite H in H2; inversion H2.
  - (* E_WhileTrue *)
    + (* b evaluates to false (contradiction) *) rewrite H in H4; inversion H4.
  - (* E_WhileTrue *)
    + (* b evaluates to true *) 
      assert (st' = st'0) as EQ1 by auto.
      subst st'. auto.
Qed.

Theorem ceval_deterministic'_alt: forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; 
      intros; inv E2...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *) 
    + (* b evaluates to false (contradiction) *) rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *) rewrite H in H5. inversion H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *) rewrite H in H2; inversion H2.
  - (* E_WhileTrue *)
    + (* b evaluates to false (contradiction) *) rewrite H in H4; inversion H4.
  - (* E_WhileTrue *)
    + (* b evaluates to true *) 
      assert (st' = st'0) as EQ1...
      subst st'...
Qed.


Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *) 
    + (* b evaluates to false (contradiction) *) rwinv H H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *) rwinv H H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *) rwinv H H2.
  - (* E_WhileTrue *)
    + (* b evaluates to false (contradiction) *) rwinv H H4.
  - (* E_WhileTrue *)
    + (* b evaluates to true *) 
      assert (st' = st'0) as EQ1...
      subst st'...
Qed.

Ltac find_rwinv :=
  match goal with
    H1 : ?E = true,
    H2 : ?E = false
    |- _ => rwinv H1 H2
  end.

Theorem ceval_deterministic''': forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_WhileTrue *)
    + (* b evaluates to true *)
      assert (st' = st'0) as EQ1...
      subst st'0...
Qed.

Theorem ceval_deterministic'''' : forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *. auto.
  - (* E_WhileTrue *)
    + (* b evaluates to true *)
      rewrite (IHE1_1 st'0 H3) in *. auto.
Qed.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic''''': forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv;
    repeat find_eqn; auto.
Qed.

Module Repeat.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall st st' st'' c1 c2,
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall b c1 c2 st st',
      beval st b = true ->
      ceval st c1 st' ->
      ceval st (IFB b THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall b c1 c2 st st',
      beval st b = false ->
      ceval st c2 st' ->
      ceval st (IFB b THEN c1 ELSE c2 FI) st'
  | E_WhileFalse : forall b c st,
      beval st b = false ->
      ceval st (WHILE b DO c END) st
  | E_WhileTrue : forall b c st st' st'',
      beval st b = true ->
      ceval st c st' ->
      ceval st' (WHILE b DO c END) st'' ->
      ceval st (WHILE b DO c END) st''
  | E_RepeatEnd : forall b c st st',
      ceval st c st' ->
      beval st b = true ->
      ceval st (CRepeat c b) st'
  | E_RepeatLoop : forall b c st st' st'',
      ceval st c st' ->
      beval st b = false ->
      ceval st' (CRepeat c b) st'' ->
      ceval st (CRepeat c b) st''.

Notation "c1 '|' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).


Theorem ceval_deterministic: forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2; try find_rwinv;
  repeat find_eqn; auto.
Qed.

End Repeat.

Example ceval_example1:
  (X ::= 2;;
   IFB X <= 1
    THEN Y ::= 3
    ELSE Z ::= 4
   FI)
  / { --> 0 }
  \\ { X --> 2 ; Z --> 4 }.
Proof.
  (* We supply the intermediate state st'... *)
  apply E_Seq with { X --> 2 }.
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.


Example ceval'_example1:
  (X ::= 2;;
   IFB X <= 1
    THEN Y ::= 3
    ELSE Z ::= 4
   FI)
  / { --> 0 }
  \\ { X --> 2 ; Z --> 4 }.
Proof.
  eapply E_Seq. (* 1 *)
  - apply E_Ass. (* 2 *)
    reflexivity. (* 3 *)
  - (* 4 *) apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := { X --> 1 ; Y --> 2 }.
Definition st21 := { X --> 2 ; Y --> 1 }.

Example eauto_example : exists s',
  (IFB X <= Y
     THEN Z ::= Y - X
     ELSE Y ::= X + Z
   FI) / st21 \\ s'.
Proof. eauto. Qed.




























