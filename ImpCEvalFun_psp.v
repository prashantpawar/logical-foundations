Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith.
Require Import Imp Maps.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => { --> 0 }
  | S i' =>
    match c with
    | SKIP =>
        st
    | l ::= a1 =>
        st & { l --> (aeval st a1) }
    | c1 ;; c2 =>
        let st' := ceval_step2 st c1 i' in
        ceval_step2 st' c2 i'
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step2 st c1 i'
          else ceval_step2 st c2 i'
    | WHILE b1 DO c1 END =>
        if (beval st b1)
        then let st' := ceval_step2 st c1 i' in
            ceval_step2 st' c i'
        else st
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
      match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (st & { l --> (aeval st a1) })
      | c1 ;; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
      end
 end.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (st & { l --> (aeval st a1)})
      | c1 ;; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Compute
  (test_ceval { --> 0}
      (X ::= 2;;
       IFB (X <= 1)
          THEN Y ::= 3
          ELSE Z ::= 4
       FI)).

(* Exercise: 2 stars, recommended (pup_to_n) *)

Definition pup_to_n : com :=
  (WHILE (1 <= X) DO
    Y ::= Y + X;;
    X ::= X - 1
  END).

(* Compute test_ceval {X --> 5} pup_to_n. *)

Example pup_to_n_1 :
  test_ceval {X --> 5} pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(* Exercise: 2 stars, optional (peven) *)
Definition peven : com :=
  (WHILE (2 <= X) DO
    X ::= X - 2;;
    Z ::= X
   END).

(* Compute test_ceval {X --> 10} peven. *)

Example peven_1 :
  test_ceval {X --> 8} peven
  = Some (0, 0, 0).
Proof.
  reflexivity.
Qed.

Example peven_2 :
  test_ceval {X --> 81} peven
  = Some (1, 0, 1).
Proof.
  reflexivity.
Qed.

(* Relational vs. Step-Indexed Evaluation *)
Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st \\ st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - (* i = 0 -- contradictory *)
    intros c st st' H. inversion H.

  - (* i = S i' *)
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      + (* SKIP *) apply E_Skip.
      + (* ::= *) apply E_Ass. reflexivity.

      + (* ;; *)
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * (* Evaluation of r1 terminates normally *)
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        * (* Otherwise -- contradiction *)
          inversion H1.

      + (* IFB *)
        destruct (beval st b) eqn:Heqr.
        * (* r = true *)
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * (* r = false *)
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      + (* WHILE *) destruct (beval st b) eqn :Heqr.
        * (* r = true *)
         destruct (ceval_step st c i') eqn:Heqr1.
         { (* r1 = Some s *)
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. simpl in H1. assumption. }
         { (* r1 = None *) inversion H1. }
        * (* r = false *)
          inversion H1.
          apply E_WhileFalse.
          rewrite <- Heqr. subst. reflexivity.  Qed.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. inversion Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    destruct c.
    + (* SKIP *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ::= *)
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + (* ;; *)
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* st1'o = None *)
        inversion Hceval.

    + (* IFB *)
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + (* WHILE *)
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * (* st1'o = Some *)
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * (* i1'o = None *)
        simpl in Hceval. inversion Hceval.  Qed.


Lemma le_n_0_eq_inv : forall n,
  0 = n -> n <= 0.
Proof.
  induction n; intros.
  - reflexivity.
  - inversion H.
Qed.

Theorem ceval__ceval_step: forall c st st',
  c / st \\ st' ->
  exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  induction Hce.
  - (* SKIP *) exists 1. simpl. reflexivity.
  - (* ::= *) exists 1. simpl. rewrite H. reflexivity.
  - (* ;; *) inversion IHHce1 as [i1 E1].
    inversion IHHce2 as [i2 E2].
    apply ceval_step_more with (i2:=i1 + i2) in E1.
    + apply ceval_step_more with (i2:=i1 + i2) in E2.
      * exists (S (i1 + i2)). simpl. rewrite E1. apply E2.
      * apply le_plus_r.
    + apply le_plus_l.
  - (* IFB true *) destruct IHHce as [i IHHce].
    destruct b;
      try (exists (S i); simpl; trivial);
      try (inversion H);
      try (rewrite H1; assumption).
   - (* IFB false *) destruct IHHce as [i IHHce].
    destruct b;
      try (exists (S i); simpl; trivial);
      try (inversion H);
      try (rewrite H1; assumption).
   - (* WHILE false *)
    destruct b;
      try (inversion H);
      try (exists 2; reflexivity);
      try (exists 2; simpl; rewrite H1; reflexivity).
   - (* WHILE true *)
     inversion IHHce1 as [i1 E1].
     inversion IHHce2 as [i2 E2].
     apply ceval_step_more with (i2:=i1 + i2) in E1.
     + apply ceval_step_more with (i2:=i1 + i2) in E2.
       * exists (S (i1 + i2)); simpl. rewrite H. rewrite E1. apply E2.
       * apply le_plus_r.
     + apply le_plus_l.
Qed.

Theorem ceval_and_ceval_step_coincide: forall c st st',
  c / st \\ st' 
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* Determination of Evaluation Again *)

Theorem ceval_deterministic' : forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval_and_ceval_step_coincide in He1.
  apply ceval_and_ceval_step_coincide in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2:=i1 + i2) in E1.
  - apply ceval_step_more with (i2:=i1 + i2) in E2.
    + rewrite E1 in E2. inversion E2. reflexivity.
    + apply le_plus_r.
  - apply le_plus_l.
Qed.