Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
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

(* Reasoning about Imp programs *)

Theorem plus2_spec : forall st n st',
    st X = n ->
    plus2 / st \\ st' ->
    st' X = (n + 2).
Proof.
  intros st n st' H1 H2.
  inversion H2. subst. clear H2. simpl.
  apply t_update_eq.
Qed.

(* Exercise: 3 stars, recommended (XtimesYinZ_spec) *)

Theorem XtimesYinZ_spec : forall st n m st',
  st X = n ->
  st Y = m ->
  XtimesYinZ / st \\ st' ->
  st' Z = (n * m).
Proof.
  intros st n m st' H1 H2 Heq.
  inversion Heq. subst. clear Heq. simpl.
  apply t_update_eq.
Qed.

(* Exercise: 3 stars, recommended (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END) as loopdef
           eqn:Heqloopdef.
  induction contra;
    try (inversion Heqloopdef).
  - subst. inversion H.
  - subst. apply IHcontra2. apply Heqloopdef.
Qed.

(* Exercise: 3 stars (no_whiles_eqv) *)
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END =>
      false
  end.

Inductive no_whilesR : com -> Prop :=
  | NoW_Skip :
      no_whilesR SKIP 
  | NoW_Ass : forall X n,
      no_whilesR (X ::= n)
  | NoW_Seq : forall c1 c2,
      no_whilesR c1 ->
      no_whilesR c2 ->
      no_whilesR (c1 ;; c2)
  | NoW_If : forall b ct cf,
      no_whilesR ct ->
      no_whilesR cf ->
      no_whilesR (IFB b THEN ct ELSE cf FI).

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros.
    induction c.
    + simpl. apply NoW_Skip.
    + simpl. apply NoW_Ass.
    + simpl. simpl in H. apply andb_true_iff in H. destruct H. apply NoW_Seq.
      * apply IHc1. apply H.
      * apply IHc2. apply H0.
    + simpl in H. apply andb_true_iff in H. destruct H. apply NoW_If.
      * apply IHc1. apply H.
      * apply IHc2. apply H0.
    + simpl in H. inversion H.
  - intros. induction c;
      try (reflexivity).
      + simpl. apply andb_true_iff. inversion H. split.
        * apply IHc1. assumption.
        * apply IHc2. assumption.
      + simpl. apply andb_true_iff. inversion H. split.
        * apply IHc1. assumption.
        * apply IHc2. assumption.
      + inversion H.
Qed.

(* Exercise: 4 stars (no_whiles_terminating) *)
Theorem no_whiles_terminating : forall c (st st':state),
  no_whilesR c->
  exists st', c / st \\ st'.
Proof.
  intros.
  generalize dependent st.
  induction c; intros.
  - (* CSkip *) exists st. apply E_Skip.
  - (* CAss *) exists (st & { s --> (aeval st a) }). apply E_Ass. reflexivity.
  - (* CSeq *) inversion H. 
    apply IHc1 with st in H2. inversion H2. subst.
    apply IHc2 with x in H3. inversion H3. exists x0.
    apply E_Seq with x.
    + apply H4.
    + apply H0.
  - (* CIf *)
      induction b.
      + (* BTrue *) inversion H. subst.
        apply IHc1 with st in H2. inversion H2.
        exists x. apply E_IfTrue.
          * reflexivity.
          * apply H0.
      + (* BFalse *) inversion H. subst.
        apply IHc2 with st in H4. inversion H4.
        exists x. apply E_IfFalse.
          * reflexivity.
          * apply H0.
      + (* BEq *) inversion H. subst.
        apply IHc1 with st in H2. inversion H2.
        apply IHc2 with st in H4. inversion H4.
        remember (beq_nat (aeval st a) (aeval st a0)) as A.
        destruct A.
          * exists x. apply E_IfTrue.
            { unfold beval. rewrite HeqA. reflexivity. }
            { apply H0. }
          * exists x0. apply E_IfFalse.
            { unfold beval. rewrite HeqA. reflexivity. }
            { apply H1. }
       + (* BLe *) inversion H. subst.
          apply IHc1 with st in H2. inversion H2.
          apply IHc2 with st in H4. inversion H4.
          remember (leb (aeval st a) (aeval st a0)) as A.
          destruct A.
          * exists x. apply E_IfTrue.
            { unfold beval. rewrite HeqA. reflexivity. }
            { apply H0. }
          * exists x0. apply E_IfFalse.
            { unfold beval. rewrite HeqA. reflexivity. }
            { apply H1. }
        + (* BNot *) inversion H. subst.
          apply IHc1 with st in H2. inversion H2.
          apply IHc2 with st in H4. inversion H4.
          remember (beval st (! b)) as A. destruct A.
          * exists x. apply E_IfTrue.
            { rewrite HeqA. reflexivity. }
            { apply H0. }
          * exists x0. apply E_IfFalse.
            { rewrite HeqA. reflexivity. }
            { apply H1. }
        + (* BAnd *) inversion H. subst.
          apply IHc1 with st in H2. inversion H2.
          apply IHc2 with st in H4. inversion H4.
          remember (beval st (b1 && b2)) as A. destruct A.
          * exists x. apply E_IfTrue.
            { rewrite HeqA. reflexivity. }
            { apply H0. }
          * exists x0. apply E_IfFalse.
            { rewrite HeqA. reflexivity. }
            { apply H1. }
  - (* CWhile *) inversion H.
Qed.

(* Additional Exercises *)

(* Exercise: 3 stars (stack_compiler) *)
Inductive sinstr : Type :=
  | SPush : nat -> sinstr
  | SLoad : string -> sinstr
  | SPlus : sinstr
  | SMinus : sinstr
  | SMult : sinstr.

Definition first_el (l : list nat) : nat := hd 0 l.
Definition second_el (l : list nat) : nat := first_el (tl l).

Definition pop2 {X:Type} (x : list X) := tl (tl x).

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | nil => stack
  | i :: t =>
      match (i,stack) with
      | (SPush n, _)  => s_execute st (n :: stack) t
      | (SLoad x, _) => s_execute st ((st x) :: stack) t
      | (SPlus, a::b::stack') => s_execute st ((b + a) :: stack') t
      | (SPlus, _) => s_execute st stack t
      | (SMinus, a::b::stack') => s_execute st ((b - a) :: stack') t
      | (SMinus, _) => s_execute st stack t
      | (SMult, a::b::stack') => s_execute st ((b * a) :: stack') t
      | (SMult, _) => s_execute st stack t
      end
  end.

Example s_execute1 :
  s_execute { --> 0 } []
    [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof.
  unfold s_execute. reflexivity.
Qed.

Example s_execute2 :
  s_execute { X --> 3 } [3;4]
    [SPush 4; SLoad X; SMult; SPlus]
  = [15; 4].
Proof.
  unfold s_execute. reflexivity.
Qed.

Example s_execute3 :
  s_execute { --> 0 } [3;4]
    [SMult; SPlus; SMinus]
  = [12].
Proof.
  unfold s_execute. reflexivity.
Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile (X - (2 * Y))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  unfold s_compile. reflexivity.
Qed.

(* Exercise: 4 stars, advanced (stack_compiler_correct) *)
Lemma app_plus : forall T x (l : list T),
  x :: l = [x] ++ l.
Proof.
  reflexivity.
Qed.

Lemma s_execute_concat_program : 
  forall (st : state) (prog1 prog2 : list sinstr) (l: list nat),
  s_execute st l (prog1 ++ prog2) = s_execute st (s_execute st l prog1) prog2.
Proof.
  intros st.
  induction prog1.
  - (* prog1 = [] *) intros. simpl. reflexivity.
  - (* prog1 = a :: prog1 *) intros. rewrite app_plus. 
    destruct a;
      try (apply IHprog1).
    + (* SPlus n *) rewrite app_assoc_reverse. 
      induction l.
      * simpl. apply IHprog1.
      * induction l.
        { - simpl. apply IHprog1. }
        { - apply IHprog1. }
    + (* SLoad s *) rewrite app_assoc_reverse. 
      induction l.
      * simpl. apply IHprog1.
      * induction l.
        { - simpl. apply IHprog1. }
        { - apply IHprog1. }
    + (* SPlus *) rewrite app_assoc_reverse. 
      induction l.
      * simpl. apply IHprog1.
      * induction l.
        { - simpl. apply IHprog1. }
        { - apply IHprog1. }
Qed.

Lemma s_compile_correct_l : forall (st : state) (e : aexp) (l: list nat),
  s_execute st l (s_compile e) = aeval st e :: l.
Proof.
  intros.
  generalize dependent l.
  induction e; intros.
  - (* ANum *) reflexivity.
  - (* AId *) reflexivity.
  - (* APlus *) simpl.
    rewrite s_execute_concat_program. rewrite IHe1.
    rewrite s_execute_concat_program. rewrite IHe2. reflexivity.
  - (* AMinus *) simpl.
    rewrite s_execute_concat_program. rewrite IHe1.
    rewrite s_execute_concat_program. rewrite IHe2. reflexivity.
  - (* AMult *) simpl.
    rewrite s_execute_concat_program. rewrite IHe1.
    rewrite s_execute_concat_program. rewrite IHe2. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_correct_l.
Qed.

(* Exercise: 3 stars, optional (short circuit) *)

Fixpoint beval_short_circuit (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b => negb (beval_short_circuit st b)
  | BAnd BFalse b => false
  | BAnd b1 b2 => andb (beval_short_circuit st b1) (beval_short_circuit st b2)
  end.

Example bexp_shortcut_1 : 
  beval { X --> 5 } (false && !(X <= 4))
  = false.
Proof.
  reflexivity.
Qed.

Theorem beval_short_circuit_correct : forall (st : state) (b : bexp),
  beval st b = beval_short_circuit st b.
Proof.
  induction b;
    try (reflexivity).
  - simpl. rewrite IHb. reflexivity.
  - simpl. destruct b1; 
            try (reflexivity);
            try (rewrite IHb2; reflexivity);
            try (rewrite IHb1; rewrite IHb2; reflexivity).
Qed.

Module BreakImp.

(* Exercise: 4 stars, advanced (break_imp) *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com (* <-- new *)
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).


Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ SContinue / st 
  | E_Break : forall st,
      BREAK / st \\ SBreak / st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
     (x ::= a1) / st \\ SContinue / st & { x --> n }
  | E_Seq_Break : forall c1 c2 st st',
      c1 / st \\ SBreak / st' ->
      (c1 ;; c2) / st \\ SBreak / st'
  | E_Seq_Continue : forall c1 c2 st st' st'' s,
      c1 / st \\ SContinue / st' ->
      c2 / st' \\ s / st'' ->
      (c1 ;; c2) / st \\ SContinue / st''
  | E_IfTrue_Break : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ SBreak / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ SBreak / st'
  | E_IfTrue_Continue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ SContinue / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ SContinue / st'
  | E_IfFalse_Break : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ SBreak / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ SBreak / st'
  | E_IfFalse_Continue : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ SContinue / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ SContinue / st'
  | E_WhileFalse : forall b c st,
      beval st b = false ->
      (WHILE b DO c END) / st \\ SContinue / st
  | E_WhileTrue_Break : forall st st' b c,
      beval st b = true ->
      c / st \\ SBreak / st' ->
      (WHILE b DO c END) / st \\ SContinue / st'
  | E_WhileTrue_Continue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ SContinue / st' ->
      (WHILE b DO c END) / st' \\ SContinue / st'' ->
      (WHILE b DO c END) / st \\ SContinue / st''

where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Example ceval_example2:
    (X ::= 2;;
     IFB X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI)
   / { --> 0 } \\ SContinue / { X --> 2 ; Z --> 4 }.
Proof.
  apply E_Seq_Continue with (st':={ X --> 2 }) (s:=SContinue).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse_Continue.
    + reflexivity.
    + apply E_Ass.
     reflexivity.
Qed.

Theorem break_ignore : forall c st st' s,
  (BREAK;; c) / st \\ s / st' ->
  st = st'.
Proof.
  induction s.
  - intros. inversion H. subst. inversion H2.
  - intros. inversion H. subst. inversion H3. reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  destruct b;
    try (intros; inversion H; subst; reflexivity).
Qed.

(* Found a bug in my implementation of ceval while trying to prove this *)
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  destruct b;
    try (intros; inversion H);
    try (inversion H0; subst; apply E_WhileTrue_Break; assumption).
Qed.

(* Exercise: 3 stars, advanced, optional (while_break_true) *)
(* Found another bug in my implementation of ceval while trying to prove this *)
Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st \\ SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' \\ SBreak / st'.
Proof.
  intros.
  remember (WHILE b DO c END) as loop.
  induction H;
    try (inversion Heqloop);
    try (subst; clear Heqloop).
  - rewrite H in H0. inversion H0.
  - exists st. assumption.
  - clear IHceval1. apply IHceval2.
    + reflexivity.
    + assumption.
Qed.

(* Exercise: 4 stars, advanced, optional (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 r1 r2,
  c / st \\ r1 / st1 ->
  c / st \\ r2 / st2 ->
  st1 = st2 /\ r1 = r2.
Proof.
  intros c st st1 st2 r1 r2 E1 E2.
  generalize dependent r2.
  generalize dependent st2.
  induction E1;
    intros st2 r2 E2;
    inversion E2; subst;
    try (split; reflexivity);
    try (apply IHE1; assumption);
    try (apply IHE1 in H1; destruct H1 as [H11 H12]; subst; inversion H12);
    try (apply IHE1_1 in H4; destruct H4 as [H13 H14]; inversion H14);
    try (destruct (beval st b); try inversion H6; try inversion H);
    try (inversion H2);
    try (apply IHE1 in H6; destruct H6 as [H15 H16]; split; trivial);
    try (apply IHE1 in H3; destruct H3 as [H17 H18]; inversion H18);
    try (rewrite H5 in H; inversion H);
    try (subst; apply IHE1_1 in H6; inversion H6; inversion H4).
  - apply IHE1_1 in H1. destruct H1 as [H19 H20]. rewrite <- H19 in H5.
    apply IHE1_2 in H5. destruct H5 as [H21 H22]. split; assumption.
  - subst. inversion E1_1.
  - subst. apply IHE1_1 in H6. destruct H6 as [H23 H24]. inversion H24.
  - clear H; clear H2. clear E1_1; clear E1_2. apply IHE1_1 in H3. 
    destruct H3 as [H25 H26]. rewrite <- H25 in H7. apply IHE1_2 in H7. assumption.
Qed.

End BreakImp.

(* Exercise: 4 stars, optional (add_for_loop) *)















































