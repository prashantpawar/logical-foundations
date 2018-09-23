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

(* Exercise: 2 stars, advanced, optional (WHILE_false_informal) *)

(*
Theorem: if b is equivalent to BFalse then (WHILE b DO c END) / st \\ st' is equivalent to SKIP / st \\ st'.

Proof:
  In order to show that if b is equivalent to BFalse then (WHILE b DO c END) / st \\ st' is equivalent to SKIP / st \\ st' we need to show that  and .

  * -> If b is equivalent to BFalse then (WHILE b DO c END) / st \\ st' implies SKIP / st \\ st'.

  + Suppose (WHILE b DO c END) / st \\ st' is derived via E_WhileFalse then st = st'. This shows SKIP / st \\ st' from the definition of E_Skip.
  + Suppose (WHILE b DO c END) / st \\ st' is derived via E_WhileTrue then that implies that beval b = true. But from our hypothesis, beval b = false, a contradiction.

  * <- If b is equivalent to BFalse then SKIP / st \\ st' implies (WHILE b DO c END) / st \\ st'.

  If we apply E_WhileFalse to (WHILE b DO c END) / st \\ st' we get st = st'. also SKIP / st \\ st' implies st = st'. Therefore (WHILE b DO c END) / st \\ st'.
*)

(* Lemma: If b is equivalent to BTrue, then it cannot be the case that (WHILE b DO c END) / st \\ st'.

  Proof: Suppose (WHILE b DO c END) / st \\ st'. We can show my induction on the derivation of (WHILE b DO c END) / st \\ st' that this assumption leads to a contradiction.

    * Suppose (WHILE b DO c END) / st \\ st' is proven by E_WhileFalse. This implies that beval b = false. But we know that b = BTrue, that means beval BTrue = false, a contradiction.
    * Suppose (WHILE b DO c END) / st \\ st' is proven by E_WhileTrue. Then we are given the induction hypothesis that (WHILE b DO c END) / st \\ st' is not true, which is exactly what we are trying to prove!
    * Since these are the only rules that could have been used to prove (WHILE b DO c END) / st \\ st', the other cases of the induction are immediately contradictory.
*)

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* rewrite is able to instantiate the quantifier in st *)
    rewrite Hb in H. inversion H.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity. Qed.

(* Exercise: 2 stars, optional (WHILE_true_nonterm_informal) *)

(* Lemma WHILE_true_nonterm means that if the term b of (WHILE b DO c END) / st \\ st' is literally equal to BTrue, then the loop will never terminate. *)

(* Exercise: 2 stars, recommended (WHILE_true) *)
Theorem WHILE_true: forall b c,
  bequiv b true ->
  cequiv
    (WHILE b DO c END)
    (WHILE true DO SKIP END).
Proof.
  intros b c Hb.
  intros st st'.
  split; intros H.
  - (* -> *) simpl. apply WHILE_true_nonterm with (c:=c) (st:=st) (st':=st') in Hb. unfold not in Hb. exfalso. apply Hb. apply H.
  - (* <- *) simpl. simpl in H. apply WHILE_true_nonterm in H.
    + exfalso. assumption.
    + unfold bequiv. intros. reflexivity.
Qed.

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  split; intros H.
  - (* -> *) induction H;
    try (inversion Heqcw; subst; clear Heqcw).
    + apply E_IfFalse; auto. apply E_Skip.
    + apply E_IfTrue; auto. apply E_Seq with st'; auto.
  - (* <- *) inversion H; subst.
    + inversion H6; subst. apply E_WhileTrue with st'0; auto.
    + inversion H6; subst. apply E_WhileFalse; auto.
Qed.

(* Exercise: 2 stars, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros c1 c2 c3 st st'.
  split; intros.
  - (* -> *) inversion H; subst. inversion H2; subst. 
    apply E_Seq with st'1; auto. apply E_Seq with st'0; auto.
  - (* <- *) inversion H; subst. inversion H5; subst.
    apply E_Seq with st'1; auto. apply E_Seq with st'0; auto.
Qed.

Theorem identity_assignment : forall (X:string),
  cequiv
    (X ::= X)
    SKIP.
Proof.
  intros X st st'.
  split; intros H.
  - (* -> *) inversion H; subst. simpl in *.
    replace (st & {X --> st X}) with st.
    + apply E_Skip.
    + apply functional_extensionality.
      rewrite t_update_same. reflexivity.
  - (* <- *) replace st' with (st' & {X --> st' X}).
    + inversion H; subst. apply E_Ass. reflexivity.
    + apply functional_extensionality. rewrite t_update_same. reflexivity.
Qed.

(* Exercise: 2 stars, recommended (assign_aequiv) *)
Theorem assign_aequiv : forall (X:string) e,
  aequiv X e ->
  cequiv SKIP (X ::= e).
Proof.
  intros X e Ha st st'.
  split; intros H.
  - (* -> *) replace st' with (st' & {X --> st' X}).
    + inversion H; subst. apply E_Ass. 
      unfold aequiv in Ha. simpl in Ha. rewrite Ha. reflexivity.
    + apply functional_extensionality. rewrite t_update_same. reflexivity.
  - (* -> *) replace st with (st & {X --> st X}).
    + inversion H; subst. unfold aequiv in Ha. simpl in Ha. rewrite Ha. apply E_Skip.
    + apply functional_extensionality. rewrite t_update_same. reflexivity.
Qed.

(* Exercise: 2 stars (equiv_classes) *)
Definition prog_a : com :=
  WHILE ! (X <= 0) DO
    X ::= X + 1
  END.
Definition prog_b : com :=
  IFB X = 0 THEN
    X ::= X + 1;;
    Y ::= 1
  ELSE
    Y ::= 0
  FI;;
  X ::= X - Y;;
  Y ::= 0.
Definition prog_c : com :=
  SKIP.
Definition prog_d : com :=
  WHILE ! (X = 0) DO
    X ::= (X * Y) + 1
  END.
Definition prog_e : com :=
  Y ::= 0.
Definition prog_f : com :=
  Y ::= X + 1;;
  WHILE ! (X = Y) DO
    Y ::= X + 1
  END.
Definition prog_g : com :=
  WHILE true DO
    SKIP
  END.
Definition prog_h : com :=
  WHILE ! (X = X) DO
    X ::= X + 1
  END.
Definition prog_i : com :=
  WHILE ! (X = Y) DO
    X ::= Y + 1
  END.

Definition equiv_classes : list (list com) :=
  [ [prog_a;prog_g;prog_f;prog_d] ;
    [prog_c;prog_h] ;
    [prog_b;prog_e] ;
    [prog_i] ].

(* Properties of Behavioral Equivalence *)
Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 Ha st.
  unfold aequiv in Ha. rewrite Ha. reflexivity.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 ->
  aequiv a2 a3 ->
  aequiv a1 a3.
Proof.
  intros a1 a2 a3 Ha1 Ha2 st.
  unfold aequiv in *. rewrite Ha1. rewrite Ha2. reflexivity.
Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  intros b st.
  reflexivity.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 ->
  bequiv b2 b1.
Proof.
  intros b1 b2 Hb st.
  unfold bequiv in Hb. rewrite Hb. reflexivity.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 ->
  bequiv b2 b3 ->
  bequiv b1 b3.
Proof.
  intros b1 b2 b3 Hb1 Hb2 st.
  unfold bequiv in *. rewrite Hb1. rewrite Hb2. reflexivity.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  intros c st st'.
  split; intros H; assumption.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 ->
  cequiv c2 c1.
Proof.
  intros c1 c2 Hc st st'. unfold cequiv in Hc.
  split; intros H.
  - rewrite Hc; assumption.
  - rewrite <- Hc; assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H1 H2.
  split; rewrite H1; rewrite H2; intros; assumption.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 ->
  cequiv c2 c3 ->
  cequiv c1 c3.
Proof.
  intros c1 c2 c3 Hc1 Hc2 st st'.
  unfold cequiv in *.
  split; intros H.
  - rewrite <- Hc2. rewrite <- Hc1. assumption.
  - rewrite Hc1. rewrite Hc2. assumption.
Qed.

(* Behavioral Equivalence is a Congruence *)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a1' Heqv st st'.
  unfold aequiv in Heqv.
  split; intros Hceval;
  try (inversion Hceval; subst; apply E_Ass; rewrite Heqv; reflexivity).
Qed.

(* Theorem: Equivalence is a congruence for WHILE - that is, if b1 is equivalent to b1' and c1 is equivalent to c1', then WHILE b1 DO c1 END is equivalent to WHILE b1' DO c1' END.

Proof: Suppose b1 is equivalent to b1' and c1 is equivalent to c1'. We must show that for every st and st,
  WHILE b1 DO c1 END / st \\ st' 
  is equivalent to 
  WHILE b1' DO c1' END / st \\ st'.

  * (->) We show that WHILE b1 DO c1 END / st \\ st' implies WHILE b1' DO c1' END / st \\ st', by induction on the derivation of WHILE b1 DO c1 END / st \\ st'. The only non-trivial cases are when the final rule of the derivation is E_WhileTrue and E_WhileFalse.
    + Lets suppose that WHILE b1 DO c1 END / st \\ st' is proven by E_WhileFalse. This implies that beval b1 = false and that st = st'. This implies that beval b1' = false, since b1 and b1' are equivalent. From this we can infer that WHILE b1' DO c1' END / st \\ st'.
    + Lets suppose that WHILE b1 DO c1 END / st \\ st' is proven by E_WhileTrue. This implies that beval b1 = true and beval b1' = true, and also WHILE b1 DO c1 END / st'0 \\ st' for some st'0, with the induction hypothesis WHILE b1' DO c1' END / st'0 \\ st'.
     Since c1 and c1' are equivalent, we know that c1 / st \\ st'0. And since b1 and b1' are equivalent, we have beval b1' = true.
     Applying E_WhileTrue, we get WHILE b1' DO c1' END / st \\ st'.

  * (<-) Similar.
*)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv, cequiv.
  intros b1 b1' c1 c1' Hb Hc st st'.
  split; intros Hce.
  - (* -> *) remember (WHILE b1 DO c1 END) as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *) apply E_WhileFalse. rewrite <- Hb. assumption.
    + (* E_WhileTrue *) apply E_WhileTrue with st'.
      * (* show loop runs *) rewrite <- Hb. assumption.
      * (* body execution *) rewrite <- Hc. assumption.
      * (* subsequent loop execution *) apply IHHce2. reflexivity.
  - (* <- *) remember (WHILE b1' DO c1' END) as cwhile eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *) apply E_WhileFalse. rewrite Hb. assumption.
    + (* E_WhileTrue *) apply E_WhileTrue with st'.
      * (* show loop runs *) rewrite Hb. assumption.
      * (* body execution *) rewrite Hc. assumption.
      * (* subsequent loop execution *) apply IHHce2. reflexivity.
Qed.

(* Exercise: 3 stars, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  intros c1 c1' c2 c2' Hc1 Hc2 st st'.
  unfold cequiv in *.
  split; intros H.
  - (* -> *) remember (c1';;c2') as cseq eqn:Hcseq.
    inversion H; subst.
    induction H;
      try (apply E_Seq with st'0; 
        try (rewrite <- Hc1; auto); 
        try(rewrite <- Hc2; auto)).
   - (* <- *) remember (c1;;c2) as cseq eqn:Hcseq.
     inversion H; subst.
     induction H;
      try (apply E_Seq with st'0; 
        try (rewrite Hc1; auto); 
        try(rewrite Hc2; auto)).
Qed.

(* Exercise: 3 stars, (CIf_congruence) *)
Theorem CIf_congruence : forall b1 b1' c1 c1' c2 c2',
  bequiv b1 b1' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b1 THEN c1 ELSE c2 FI) (IFB b1' THEN c1' ELSE c2' FI).
Proof.
  intros b1 b1' c1 c1' c2 c2' Hb Hc1 Hc2 st st'.
  unfold bequiv, cequiv in *.
  split; intros Hceval.
  - (* -> *) remember (IFB b1' THEN c1' ELSE c2' FI) as cif eqn:Hcif.
    inversion Hceval; subst.
    + (* E_IfTrue *) apply E_IfTrue.
      * (* condition evaluation *) rewrite <- Hb. assumption.
      * (* then body *) rewrite <- Hc1. assumption.
    + (* E_IfFalse *) apply E_IfFalse.
      * (* condition evaluation *) rewrite <- Hb. assumption.
      * (* else body *) rewrite <- Hc2. assumption.
   - (* <- *) remember (IFB b1 THEN c1 ELSE c2 FI) as cif eqn:Hcif.
    inversion Hceval; subst.
    + (* E_IfTrue *) apply E_IfTrue.
      * (* condition evaluation *) rewrite Hb. assumption.
      * (* then body *) rewrite Hc1. assumption.
    + (* E_IfFalse *) apply E_IfFalse.
      * (* condition evaluation *) rewrite Hb. assumption.
      * (* else body *) rewrite Hc2. assumption.
Qed.

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= 0;;
     IFB X = 0
     THEN
      Y ::= 0
     ELSE
      Y ::= 42
     FI)
    (* Program 2: *)
    (X ::= 0;;
     IFB X = 0
     THEN
      Y ::= X - X (* <--- changed here *)
     ELSE
      Y ::= 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl. symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

(* Exercise: 3 strars, advanced, optional (not_congr) *)

(* We've shown that the cequiv relation is both an equivalence and a congruence on commands. Can you think of a relation on commands that is an equivalence but not a congruence? *)

(* Program Transformations *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* Consant-Folding Transformation *)
Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.


(* needed for parsing the examples below *)
Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

Example fold_aexp_ex1 :
  fold_constants_aexp ((1 + 2) * X) = (3 * X).
Proof.
  reflexivity.
Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp (X - ((0 * 6) + Y)) = (X - (0 + Y)).
Proof.
  reflexivity.
Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') => BEq a1' a2'
    end
   | BLe a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => if leb n1 n2 then BTrue else BFalse
    | (a1', a2') => BLe a1' a2'
    end
   | BNot b => 
      match (fold_constants_bexp b) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b' => BNot b'
      end
   | BAnd b1 b2 => 
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ! (false && true)) = true.
Proof.
  reflexivity.
Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1)))) = ((X = Y) && true).
Proof.
  reflexivity.
Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | i ::= a => CAss i (fold_constants_aexp a)
  | c1;;c2 => (fold_constants_com c1);;(fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match (fold_constants_bexp b) with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN (fold_constants_com c1) 
                     ELSE (fold_constants_com c2) FI
      end
  | WHILE b DO c END => 
      match (fold_constants_bexp b) with
      | BFalse => SKIP
      | BTrue => WHILE BTrue DO SKIP END
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.


Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= 4 + 5;;
     Y ::= X - 3;;
     IFB (X - Y) = (2 + 4) THEN
       SKIP
     ELSE
       Y ::= 0
     FI;;
     IFB 0 <= (4 - (2 + 1))
     THEN
       Y ::= 0
     ELSE
       SKIP
     FI;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)
  = (* After constant folding: *)
    (X ::= 9;;
     Y ::= X - 3;;
     IFB (X - Y) = 6 THEN
       SKIP
     ELSE
       Y ::= 0
     FI;;
     Y ::= 0;;
     WHILE Y = 0 DO
       X ::= X + 1 
     END).
Proof. reflexivity. Qed.

(* Soundness of Constant Folding *)
Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  intros a st.
  induction a; auto;
    try (simpl; rewrite IHa1, IHa2; 
         induction (fold_constants_aexp a1); 
         induction (fold_constants_aexp a2); auto).
Qed.

(* Exercise: 3 stars, optional (fold_bexp_Eq_informal) *)

(* Theorem: The constant folding function for booleans, fold_constants_bexp, is sound.

Proof: We must show that b is equivalent to fold_constants_bexp, for all boolean expression b.

  We will do that by performing induction on b. The cases for BTrue and BFalse are trivial.

  * (BEq) In this case we must show that
    beval st (BEq a1 a2)
    = beval st (fold_constants_bexp (BEq a1 a2)).

    There are two cases to consider.
    + Suppose fold_constants_aexp a1 = ANum n1 and fold_constants_aexp a2 = ANum n2 for some n1 and n2.

    In this case we have
    fold_constants_bexp (BEq a1 a2)
    = if beq_nat n1 n2 then BTrue else BFalse

    and

    beval st (BEq a1 a2)
    = beq_nat (aeval st a1) (aeval st a2).

    By the soundness of constant folding for the arithmatic expressions (Lemma fold_constants_aexp_sound), we know
      aeval st a1
    = aeval st (fold_constants_aexp a1)
    = aeval st (ANum n1)
    = n1

    and

      aeval st a2
    = aeval st (fold_constants_aexp a2)
    = aeval st (ANum n2)
    = n2

    beval st (BEq a1 a2)
    = beq_nat n1 n2.

    Similarly,
    beval st (fold_constants_bexp (BEq a1 a2))
    = beval st (if beq_nat n1 n2 then BTrue else BFalse).

    Consider n1 = n2.

    beval st (fold_constants_bexp (BEq a1 a2))
    = beval st BTrue
    = true

  also
    beval st (BEq a1 a2)
    = beq_nat n1 n2 = true

    Similarly n1 =/= n2

    beval st (fold_constants_bexp (BEq a1 a2))
    = beval st BFalse
    = false

  also
    beval st (BEq a1 a2)
    = beq_nat n1 n2 = false

  Therefore
    beval st (BEq a1 a2)
    = beval st (fold_constants_bexp (BEq a1 a2)).

   + Otherwise one of fold_constants_aexp a1 and fold_constants_aexp a2 is not a constant. In this case we must show.

    beval st (BEq a1 a2)
    = beval st (BEq (fold_constants_aexp a1) (fold_constants_aexp a2))

    which, by the definition of beval, is the same as showing

    beq_nat (aeval st a1) (aeval st a2)
    = beq_nat (aeval st (fold_constants_aexp a1))
              (aeval st (fold_constants_aexp a2))

    By the soundness of constant folding for arithmatic expressions (Lemma fold_constants_aexp_sound), we know

    aeval st a1
    = aeval st (fold_constants_aexp a1)

    and

    aevla st a2
    = aeval st (fold_constants_aexp a2)

    Replacing these definitions in our equation we get,

    beq_nat (aeval st a1) (aeval st a2)
    = beq_nat (aeval st a1) (aeval st a2)

    thereby completing the case.
*)

Theorem fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
Proof.
  intros b st.
  induction b; auto.
  - (* BEq *) simpl.
    rewrite fold_constants_aexp_sound; 
    rewrite fold_constants_aexp_sound with (a:=a0).
    induction (fold_constants_aexp a); induction (fold_constants_aexp a0); auto.
    + (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. induction (n =? n0); auto.
  - (* BLe *) simpl.
    rewrite fold_constants_aexp_sound; 
    rewrite fold_constants_aexp_sound with (a:=a0).
    induction (fold_constants_aexp a); induction (fold_constants_aexp a0); auto.
    + (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. induction (n <=? n0); auto.
  - (* BNot *) simpl. rewrite IHb.
    induction (fold_constants_bexp b); auto.
  - (* BAnd *) simpl. rewrite IHb1, IHb2.
    induction (fold_constants_bexp b1); induction (fold_constants_bexp b2); auto.
Qed.












































