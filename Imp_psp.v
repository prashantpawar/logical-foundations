Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.
Require Import Maps.

(* Arithmatic and Boolean Expressions *)

Module Aexp.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(*
1+2*3

APlus (ANum 1) (AMult (ANum 2) (ANum 3))
*)

(* Evaluation *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end. 

Example test_aeval_1:
  aeval (APlus (ANum 1) (AMult (ANum 2) (ANum 3))) = 7.
Proof.
  reflexivity.
Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(* Optimization *)

Fixpoint optimize_Oplus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_Oplus e2
  | APlus e1 e2 => 
      APlus (optimize_Oplus e1) (optimize_Oplus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_Oplus e1) (optimize_Oplus e2)
  | AMult e1 e2 =>
      AMult (optimize_Oplus e1) (optimize_Oplus e2)
  end.

Example test_optimize_Oplus:
  optimize_Oplus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = (APlus (ANum 2) (ANum 1)).
Proof.
  reflexivity.
Qed.

Lemma aeval_aplus : forall a1 a2 : aexp,
  aeval a1 + aeval a2 = aeval (APlus a1 a2).
Proof.
  intros.
  reflexivity.
Qed.

Theorem optimize_Oplus_sound: forall a:aexp,
  aeval (optimize_Oplus a) = aeval a.
Proof.
  intros.
  induction a.
  - reflexivity.
  - destruct a1.
    + destruct n.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in *. rewrite IHa2. rewrite IHa1. reflexivity.
    + simpl. rewrite IHa2. simpl in IHa1. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.


(* Coq Automation *)

Theorem silly1: forall ae, aeval ae = aeval ae.
Proof.
  try reflexivity.
Qed.

Theorem silly2: forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity.
  apply HP.
Qed.

Lemma foo : forall n, leb 0 n = true.
Proof.
  intros.
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  destruct n;
  simpl;
  reflexivity.
Qed.

Theorem optimize_Oplus_sound' : forall a,
  aeval (optimize_Oplus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  - destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
     + destruct n;
        try (simpl; rewrite IHa2; reflexivity).
Qed.

Theorem optimize_Oplus_sound'' : forall a,
  aeval (optimize_Oplus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    try reflexivity.
  - destruct a1; try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n;
      simpl; rewrite IHa2; reflexivity.
Qed.

(* The repeat Tactical *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(* Exercise: 3 stars (optimize_Oplus_b_sound) *)
Fixpoint optimize_Oplus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_Oplus a1) (optimize_Oplus a2)
  | BLe a1 a2 => BLe (optimize_Oplus a1) (optimize_Oplus a2)
  | BNot b1 => BNot b1
  | BAnd b1 b2 => BAnd b1 b2
  end.

Example test_optimize_Oplus_b:
  optimize_Oplus_b (BEq ((APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1)))))
    (APlus (ANum 2) (ANum 1))) = BEq (APlus (ANum 2) (ANum 1)) (APlus (ANum 2) (ANum 1)).
Proof.
  reflexivity.
Qed.

Theorem optimize_Oplus_b_sound : forall b,
  beval (optimize_Oplus_b b) = beval b.
Proof.
  intros.
  induction b;
    try (simpl; repeat (rewrite optimize_Oplus_sound); reflexivity).
Qed.

(* Exercise: 4 stars, optional (optimizer) *)
Fixpoint optimize_Omult (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => 
      APlus (optimize_Omult e1) (optimize_Omult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_Omult e1) (optimize_Omult e2)
  | AMult (ANum 0) e2 => (ANum 0)
  | AMult e1 e2 =>
      AMult (optimize_Omult e1) (optimize_Omult e2)
  end.

Example test_optimize_Omult:
  aeval (optimize_Omult (AMult (ANum 3)
                        (AMult (ANum 0)
                               (APlus (ANum 1) (ANum 1)))))
  = aeval (ANum 0).
Proof.
  reflexivity.
Qed.

Theorem optimize_Omult_sound : forall a,
  aeval (optimize_Omult a) = aeval a.
Proof.
  intros.
  induction a;
    try (reflexivity);
    try (simpl; simpl in IHa1; rewrite IHa1; simpl in IHa2; rewrite IHa2; reflexivity).
  - destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1; simpl in IHa2; rewrite IHa2; reflexivity).
    + destruct n.
      * reflexivity.
      * simpl. rewrite <- IHa2. reflexivity.
Qed.

Fixpoint optimize_Omult_b (b : bexp) : bexp :=
  match b with
  | BEq a1 a2 => BEq (optimize_Omult a1) (optimize_Omult a2)
  | BLe a1 a2 => BLe (optimize_Omult a1) (optimize_Omult a2)
  | _ => b
  end.

Example test_optimize_Omult_b:
  beval (optimize_Omult_b (BEq ((AMult (ANum 1)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 0)))))
    (APlus (ANum 0) (ANum 0)))) = beval (BEq (ANum 0) (APlus (ANum 0) (ANum 0))).
Proof.
  reflexivity.
Qed.

Theorem optimize_Omult_b_sound : forall b,
  beval (optimize_Omult_b b) = beval b.
Proof.
  intros.
  induction b;
    try (reflexivity);
    try (simpl; repeat (rewrite optimize_Omult_sound);reflexivity).
Qed.


(* Optimize False Shortcut *)

Fixpoint optimize_false_shortcut_b (b : bexp) : bexp :=
  match b with
  | BAnd BFalse b2 => BFalse
  | BAnd b1 b2 => BAnd b1 b2
  | _ => b
  end.

Example test_optimize_false_b_shortcut:
  beval (optimize_false_shortcut_b (BAnd (BEq (ANum 2) 
                                           (ANum 1)) 
                                      (BEq (ANum 2) 
                                           (ANum 1)))) = beval (BFalse).
Proof.
  reflexivity.
Qed.

Theorem optimize_false_shortcut_sound : forall b,
  beval (optimize_false_shortcut_b b) = beval b.
Proof.
  intros.
  induction b;
    try (reflexivity).
  - destruct b1;
      try (reflexivity).
Qed.

(* Optimize leb *)

Fixpoint optimize_le_0_b (b : bexp) : bexp :=
  match b with
  | BLe (ANum 0) b2 => BTrue
  | BLe b1 b2 => BLe b1 b2
  | _ => b
  end.

Example test_optimize_le_0:
  beval (optimize_le_0_b (BAnd (BLe (ANum 0) 
                                           (ANum 1)) 
                                      (BLe (ANum 2) 
                                           (ANum 1)))) = beval (BFalse).
Proof.
  reflexivity.
Qed.

Theorem optimize_le_0_b_sound: forall b,
  beval (optimize_le_0_b b) = beval b.
Proof.
  intros.
  induction b;
    try (reflexivity).
  - destruct a;
      try (reflexivity).
    + destruct n;
      try (reflexivity).
Qed.

Definition optimizer (a : aexp) : aexp :=
  optimize_Oplus (optimize_Omult a).

Definition optimizer_b (b : bexp) : bexp :=
  optimize_Oplus_b (optimize_Omult_b (optimize_false_shortcut_b (optimize_le_0_b b))).

Example test_optimizer:
  aeval (optimizer (APlus (ANum 1)
                          (AMult (ANum 2)
                                 (ANum 0)))) = aeval (ANum 1).
Proof.
  reflexivity.
Qed.

Theorem optimizer_sound : forall a,
  aeval (optimizer a) = aeval a.
Proof.
  intros.
  induction a;
    try (reflexivity);
    try (unfold optimizer; rewrite optimize_Oplus_sound; rewrite optimize_Omult_sound; reflexivity).
Qed.

Theorem optimizer_b_sound : forall b,
  beval (optimizer_b b) = beval b.
Proof.
  intros.
  induction b;
    try (reflexivity);
    try (unfold optimizer_b; 
         rewrite optimize_Oplus_b_sound;
         rewrite optimize_Omult_b_sound;
         rewrite optimize_false_shortcut_sound;
         rewrite optimize_le_0_b_sound;
         reflexivity).
Qed.

(* Defining New Tactic Notations *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(* Evaluation as a Relation *)
Module aevalR_first_try.

(* 
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.
  *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat),
      aevalR (ANum n) n
  | E_APlus : forall (n1 n2 : nat) (e1 e2 : aexp),
      aevalR e1 n1 -> 
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (n1 n2 : nat) (e1 e2 : aexp),
      aevalR e1 n1 -> 
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (n1 n2 : nat) (e1 e2 : aexp),
      aevalR e1 n1 -> 
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Notation "e '\\' n"
        := (aevalR e n)
           (at level 50, left associativity)
        : type_scope.

End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.


(* Equivalence of the Definitions *)

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  intros. split.
  - intros.
    induction H;
      try (reflexivity);
      try (simpl; rewrite IHaevalR1; rewrite IHaevalR2; reflexivity).
  - generalize dependent n.
    induction a;
      simpl; intros; subst; constructor;
        try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* Exercise: 3 stars (bevalR) *)

(*
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2 => leb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)


  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_Oplus a1) (optimize_Oplus a2)
  | BLe a1 a2 => BLe (optimize_Oplus a1) (optimize_Oplus a2)
  | BNot b1 => BNot b1
  | BAnd b1 b2 => BAnd b1 b2
  *)

Reserved Notation "e '|\/|' n" (at level 55, left associativity).
Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : BTrue |\/| true
  | E_BFalse : BFalse |\/| false
  | E_BEq : forall (a b: aexp) (n m: nat), (a \\ n) -> (b \\ m) -> BEq a b |\/| beq_nat n m
  | E_BLe : forall (a b: aexp) (n m: nat), (a \\ n) -> (b \\ m) -> BLe a b |\/| leb n m
  | E_BNot : forall (a: bexp) (n: bool), (a |\/| n) -> BNot a |\/| negb n
  | E_BAnd : forall (a b: bexp) (n m:bool), (a |\/| n) -> (b |\/| m) -> BAnd a b |\/| andb n m
  where "e '|\/|' n" := (bevalR e n) : type_scope. 

Example test_evalR_1:
  (APlus (ANum 1) 
         (AMult (ANum 1) (ANum 3))) \\ (1 + 1 * 3).
Proof.
  repeat constructor.
Qed.

Lemma beval_iff_bevalR' : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros.
    induction H.
    + reflexivity.
    + reflexivity.
    + simpl. apply aeval_iff_aevalR in H. apply aeval_iff_aevalR in H0.
      rewrite H, H0. reflexivity.
    + simpl. apply aeval_iff_aevalR in H. apply aeval_iff_aevalR in H0.
      rewrite H, H0. reflexivity.
    + simpl. rewrite <- IHbevalR. reflexivity.
    + simpl. rewrite <- IHbevalR1. rewrite <- IHbevalR2. reflexivity.
  - intros.
    generalize dependent bv.
    induction b.
    + intros. rewrite <- H. simpl. apply E_BTrue.
    + intros. rewrite <- H. simpl. apply E_BFalse.
    + intros. rewrite <- H. simpl. apply E_BEq.
      * apply aeval_iff_aevalR. reflexivity.
      * apply aeval_iff_aevalR. reflexivity.
    + intros. rewrite <- H. simpl. apply E_BLe.
      * apply aeval_iff_aevalR. reflexivity.
      * apply aeval_iff_aevalR. reflexivity.
    + intros. rewrite <- H. simpl. apply E_BNot. apply IHb. reflexivity.
    + intros. rewrite <- H. simpl. apply E_BAnd.
      * apply IHb1. reflexivity.
      * apply IHb2. reflexivity.
Qed.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros.
    induction H;
      try (reflexivity);
      try (simpl;
           apply aeval_iff_aevalR in H; rewrite H;
           apply aeval_iff_aevalR in H0; rewrite H0;
           reflexivity).
      + rewrite <- IHbevalR. reflexivity.
      + rewrite <- IHbevalR1. rewrite <- IHbevalR2. reflexivity.
   - intros.
      generalize dependent bv.
      induction b;
        try (intros; rewrite <- H; simpl; constructor; apply aeval_iff_aevalR; reflexivity).
      + intros. simpl. rewrite <- H. simpl. constructor. apply IHb. reflexivity.
      + intros. simpl. rewrite <- H. simpl. constructor. apply IHb1. reflexivity. apply IHb2. reflexivity.
Qed.

End Aexp.

(* Computational vs. Relational Definitions *)

Module aevalR_division.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.

Reserved Notation "e '\\' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv : forall (a1 a2 : aexp) (n1 n2 n3 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

  where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Inductive aexp : Type :=
  | AAny : aexp (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

  where "a '\\' n" := (aevalR a n) : type_scop.

End aevalR_extended.

(* Expressions with Variables *)

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp (* <-- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.



(* Notations *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.


(* Evaluation *)
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <---- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b => negb (beval st b)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Notation "{ a --> x }" := 
  (t_update { --> 0 } a x) (at level 0).
Notation "{ a --> x ; b --> y }" := 
  (t_update ({ a --> x }) b y) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z }" := 
  (t_update ({ a --> x ; b --> y }) c z) (at level 0). 
Notation "{ a --> x ; b --> y ; c --> z ; d --> t }" := 
  (t_update ({ a --> x ; b --> y ; c --> z }) d t) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v}) g w) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w ; h --> s }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v ; g --> w}) h s) (at level 0).

Example aexpl :
  aeval { X --> 5 } (3 + (X * 2))
  = 13.
Proof.
  reflexivity.
Qed.

Example bexpl : 
  beval { X --> 5 } (true && !(X <= 4))
  = true.
Proof.
  reflexivity.
Qed.

(* Commands *)

(* Syntax *)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

Open Scope com_scope.

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ! (Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END.

(* More Examples *)

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

(* Loops *)

Definition subtract_slowly : com :=
  WHILE ! (X = 0) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3;;
  Y ::= 5;;
  subtract_slowly.

(* An infinite Loop *)
Definition loop : com :=
  WHILE true DO
    SKIP
  END.

(* Evaluating Commands *)

Fixpoint ceval_fun_no_while (st : state) (c : com) 
                           : state :=
  match c with
  | SKIP => st
  | x ::= a1 =>
      st & { x --> (aeval st a1)}
  | c1 ;; c2 =>
      let st' := ceval_fun_no_while st c1 in
      ceval_fun_no_while st' c2
  | IFB b THEN c1 ELSE c2 FI =>
      if (beval st b)
        then ceval_fun_no_while st c1
        else ceval_fun_no_while st c2
  | WHILE b DO c END =>
      st (* Bogus *)
  end.

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ st & { x --> n }
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
  (X ::= 2;;
   IFB X <= 1
    THEN Y ::= 3
    ELSE Z ::= 4
   FI)
 / { --> 0 } \\ { X --> 2 ; Z --> 4 }.
Proof.
  apply E_Seq with { X --> 2}.
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
Qed.

(* Exercise: 2 stars (ceval_example2) *)

Example ceval_example2:
  (X ::= 0;; Y ::= 1;; Z ::= 2) / { --> 0 } \\
  { X --> 0; Y --> 1 ; Z --> 2}.
Proof.
  apply E_Seq with { X --> 0}.
  - apply E_Ass. reflexivity.
  - apply E_Seq with { X --> 0 ; Y --> 1}.
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

(* Exercise: 3 stars, optional (pup_to_n) *)

Definition pup_to_n : com :=
  (Y ::= 0;; (* SUM *)
  WHILE !(0 = X) DO
    Y ::= Y + X;;
    X ::= X - 1
  END).

Definition pup_to_2_ceval :
  pup_to_n / { X --> 2 }
    \\ { X --> 2 ; Y --> 0 ; Y --> 2 ; X --> 1 ; Y --> 3 ; X --> 0 }.
Proof.
  unfold pup_to_n.
  apply E_Seq with {X --> 2; Y --> 0}.
  - apply E_Ass. reflexivity.
  - apply E_WhileTrue with {X --> 2; Y --> 0; Y --> 2; X --> 1}.
    + reflexivity.
    + apply E_Seq with {X --> 2; Y --> 0; Y --> 2}.
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply E_WhileTrue with 
        {X --> 2; Y --> 0; Y --> 2; X --> 1; Y --> 3; X --> 0}.
      * reflexivity.
      * apply E_Seq with {X --> 2; Y --> 0; Y --> 2; X --> 1; Y --> 3}.
        { - apply E_Ass. reflexivity. }
        { - apply E_Ass. reflexivity. }
      * apply E_WhileFalse. reflexivity.
Qed.

(* Determination of Evaluation *)

Theorem ceval_deterministic : forall c st st1 st2,
  c / st \\ st1 ->
  c / st \\ st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1;
    intros st2 H2; inversion H2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *) assert (st' = st'0) as EQ1.
    { apply IHceval1. apply H1. }
    apply IHceval2. rewrite EQ1. apply H5.
  - (* E_IfTrue b1 is true *) apply IHceval. apply H8.
  - (* E_IfTrue b1 is false *) rewrite H in H7. inversion H7.
  - (* E_IfFalse b1 is true *) rewrite H in H7. inversion H7.
  - (* E_IfFalse b1 is false *) apply IHceval. assumption.
  - (* E_WhileFalse b1 is false *) reflexivity.
  - (* E_WhileFalse b1 is true *) rewrite H in H3. inversion H3.
  - (* E_WhileTrue b1 is false *) rewrite H in H5. inversion H5.
  - (* E_WhileTrue b1 is true *) apply IHceval2.
    assert (st' = st'0).
    { apply IHceval1. apply H4. }
    rewrite H0. apply H7.
Qed.











































