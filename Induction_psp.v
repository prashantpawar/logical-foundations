Require Export Basics_psp.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

(** Exercise: 2 stars, recommended (basic induction) **)

Theorem mult_0_r : forall n:nat, 
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = Sn' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) intros m. induction m as [| m' IHm'] 
    + (* m = 0 *) simpl. reflexivity.
    + (* m = S m' *) simpl. rewrite <- IHm'. simpl. reflexivity.
  - (* n = S n *) intros m. simpl. induction m as [| m' IHm'].
    + (* m = 0 *) simpl. rewrite <- plus_n_O_firsttry. reflexivity.
    + (* m = S m' *) simpl. rewrite <- IHm'. rewrite -> IHn'. simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite -> plus_comm. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

(** Excercise: 2 stars (double plus) **)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b as [| b'].
  - reflexivity.
  - reflexivity.
Qed.


Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n). 
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(**
Theorem: For any n and m,
  n + m = m + n
Proof: By induction on n.
  * First, suppose n = 0. We must show
    0 + m = m + 0
    This follows directly from the definition of +.
  * Next supppose n = S n', where
    n' + m = m + n'

    We must show
    (S n') + m = m + (S n')

    By the definition of +, this follows from:
    S(n' + m) = 

Aborted.
**)

(** * More Exercises *)

(** **** Exercise: 3 stars, recommended (mult_comm)  *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction on [plus_swap]. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.  You may find that [plus_swap] comes in
    handy.) *)

Theorem mult_comm_FAILED : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. 
  induction n.
  - induction m.
    + reflexivity.
    + simpl. rewrite mult_0_r. reflexivity.
  - induction m.
    + simpl. rewrite mult_0_r. reflexivity.
    + simpl. rewrite IHn. rewrite plus_comm. simpl. 
Abort.

Lemma mult_n_Sm : forall m n : nat,
    n * (S m) = n + n * m.
Proof.
  intros n m. induction m.
  - reflexivity.
  - simpl. rewrite plus_swap. rewrite IHm. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction m.
  - rewrite mult_0_r. reflexivity.
  - simpl. rewrite mult_n_Sm. rewrite IHm. reflexivity.
Qed.

(** **** Exercise: 3 stars, optional (more_exercises)  *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  (* destruct - wrong *)
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed. 

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* simpl and rewrite *)
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* simpl and rewrite - wrong *)
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  (* induction *)
  intros n m p H. induction p.
  - induction n.
    + reflexivity.
    + rewrite plus_O_n. rewrite plus_O_n. rewrite H. reflexivity.
  - induction n.
    + simpl. apply IHp.
    + simpl. apply IHp.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* simpl-rewrite *)
  intros n. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* induction - wrong *)
  intros n. destruct n.
  - reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* destruct *) 
  intros b c.
  destruct b.
  - simpl. destruct c.
    + reflexivity.
    + reflexivity.
  - simpl. destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* induction *) 
  intros n m p. induction n.
  - reflexivity.
  - simpl. induction m.
    + simpl. rewrite <- plus_n_O. rewrite <- plus_n_O. reflexivity.
    + simpl. rewrite IHn. rewrite plus_assoc. reflexivity.
Qed.

Lemma mult_O_n_m : forall n m : nat,
  (n + m) * 0 = 0.
Proof.
  intros n m. induction n.
  - rewrite mult_0_r. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* induction *)
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite IHn. reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(** Prove the following theorem.  (Putting the [true] on the left-hand
    side of the equality may look odd, but this is how the theorem is
    stated in the Coq standard library, so we follow suit.  Rewriting
    works equally well in either direction, so we will have no problem
    using the theorem no matter which way we state it.) *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* destruct *)
  intros n. induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

(** **** Exercise: 2 stars, optional (plus_swap')  *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* induction *)
  intros n m p.
  rewrite plus_assoc.
  replace (n + m) with (m + n).
  - rewrite plus_assoc. reflexivity.
  - rewrite plus_comm. reflexivity.
Qed.

(** **** Exercise: 3 stars, recommended (binary_commute)  *)
(** Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").

    Before you start working on this exercise, copy the definitions
    from your solution to the [binary] exercise here so that this file
    can be graded on its own.  If you want to change your original
    definitions to make the property easier to prove, feel free to
    do so! *)

Lemma bin_to_nat_O : forall n : bin,
  bin_to_nat n + 0 = bin_to_nat n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite <- plus_Sn_m. rewrite <- plus_n_O. reflexivity.
Qed.


Theorem bin_to_nat_pres_incr : forall n : bin,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n. induction n.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- plus_Sn_m.
    rewrite plus_comm.
    rewrite plus_n_Sm.
    rewrite bin_to_nat_O.
    rewrite <- plus_n_O. reflexivity.
Qed.


(** **** Exercise: 5 stars, advanced (binary_inverse)  *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    there to complete this one; please copy them to this file to make
    it self contained for grading.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, this is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. *)

Check Zero. (** 0 **)
Check Twice_plus_1 Zero. (** 1 **)
Check Twice (Twice_plus_1 Zero). (** 2 **)
Check Twice_plus_1 (Twice_plus_1 Zero). (** 3 **)
Check Twice (Twice (Twice_plus_1 Zero)). (** 4 **)
Check Twice_plus_1 (Twice (Twice_plus_1 Zero)). (** 5 **)
Check Twice (Twice_plus_1 (Twice_plus_1 Zero)). (** 6 **)
Check Twice_plus_1 (Twice_plus_1 (Twice_plus_1 Zero)). (** 7 **)


Fixpoint half (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (half n')
  end.

Example test_half_1: half 3 = 1.
Proof. reflexivity. Qed.

Example test_half_2: half 6 = 3.
Proof. reflexivity. Qed.

Example test_half_3: half 9 = 4.
Proof. reflexivity. Qed.

Fixpoint half_bin (n : bin) : bin :=
  match n with
  | Zero => Zero
  | Twice n' => n'
  | Twice_plus_1 n' => n'
  end.

Example test_half_bin_1: half_bin (Twice_plus_1 Zero) = Zero.
Proof. reflexivity. Qed.

Example test_half_bin_2: half_bin (Twice_plus_1 (Twice_plus_1 Zero)) = Twice_plus_1 Zero.
Proof. reflexivity. Qed.

Example test_half_bin_3: half_bin (Twice_plus_1 (Twice_plus_1 (Twice_plus_1 Zero))) = (Twice_plus_1 (Twice_plus_1 Zero)).
Proof. reflexivity. Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => Zero
  | S n' => match nat_to_bin n' with
            | Zero => Twice_plus_1 Zero
            | Twice b => Twice_plus_1 b
            | Twice_plus_1 b => Twice (incr b)
            end
  end.

Compute bin_to_nat (nat_to_bin 3).
Compute bin_to_nat (nat_to_bin 4).
Compute bin_to_nat (nat_to_bin 8).

Example test_nat_to_bin_1: nat_to_bin 0 = Zero.
Proof. reflexivity. Qed.

Example test_nat_to_bin_2: nat_to_bin 1 = Twice_plus_1 Zero.
Proof. reflexivity. Qed.

Example test_nat_to_bin_3: nat_to_bin 2 = Twice (Twice_plus_1 Zero).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_bin_4: nat_to_bin 3 = Twice_plus_1 (Twice_plus_1 Zero).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_bin_5: nat_to_bin 4 = Twice (Twice (Twice_plus_1 Zero)).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_bin_6: nat_to_bin 5 = Twice_plus_1 (Twice (Twice_plus_1 Zero)).
Proof. simpl. reflexivity. Qed.

Lemma bin_to_nat_Sn : forall n: bin,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite IHn. 
    rewrite plus_Sn_m. 
    rewrite <- plus_n_O.
    rewrite bin_to_nat_O.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Lemma nat_to_bin_Sn_O : forall n: nat,
  nat_to_bin (n + 0) = nat_to_bin (n).
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma nat_to_bin_Sn : forall n: nat,
  nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
  intros n. induction n.
  - reflexivity.
Abort.


Theorem nat_to_bin_to_nat : forall n: nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. unfold bin_to_nat. destruct n as [| n'].
    + reflexivity.
    + 
Abort.




































