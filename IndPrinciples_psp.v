Set Warnings "-notation-overridden,-parsing".
Require Export ProofObjects.

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. apply IHn'.
Qed.

(* Exercise: 2 stars, optional (plus_one_r') *)
Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite IHn'. reflexivity.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

(* Exercise: 1 star, optional (rgb) *)
Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

(* rgb_ind : forall P : rgb -> Prop,
  P red -> P green -> P blue -> forall r : rgb, P r.*)

Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

(* Exercise: 1 star, optional (natlist1) *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(* natlist1_ind : forall P : natlist1 -> Prop,
  P nnil1 ->
  (forall (ns : natlist1),
  P ns -> forall n:nat, P (nsnoc1 ns n) ->
  forall ns : natlist1, P ns *)
Check natlist1_ind.

(* Exercise: 1 star, optional (byntree_ind) *)

Inductive byntree : Type :=
  | bempty : byntree
  | bleaf : yesno -> byntree
  | nbranch : yesno -> byntree -> byntree -> byntree.

(* byntree_ind : forall P : byntree -> Prop.
  P bempty ->
  (forall (y:yesno), P (bleaf y)) ->
  (forall (y:yesno) (b : byntree),
  P b ->
  forall (b0 : byntree) P b0 -> P (nbranch y b b0)) ->
  forall b : byntree, P b *)

Check byntree_ind.

(* Exercise: 1 star, optional (ex_set) *)

(* ExSet_ind :
  forall P : ExSet -> Prop,
        (forall b : bool, P (con1 b)) ->
        (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
        forall e : ExSet, P e *)

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

(* Polymorphism *)

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list_ind.

(* Exercise: 1 star, optional (tree) *)
Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

(* tree_ind :
  forall (X : Type) (P : tree X -> Prop),
  (forall (x : X), P (leaf X x)) ->
  (forall (x : X) (t : tree X),
  P t -> 
  (forall (t0: tree X), P t0 -> P (node X t t0))) ->
  forall t : tree X, P t. *)

Check tree_ind.

(* Exercise: 1 star, optional (mytype) *)

Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

(* Exercise: 1 star, optional (foo) *)

Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

(* Exercise: 1 star, optional (foo') *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.


(*  foo'_ind :
  forall (X : Type) (P : foo' X -> Prop),
    (forall (l : list X) (f : foo' X),
        P f ->
        P (C1 X l f)) ->
    P (C2 X) ->
    forall f : foo' X, P f *)
Check foo'_ind.

(* Induction Hypotheses *)
Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn.
Qed.


(* More on the 'induction' tactic *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. simpl. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.


Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [| m'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* Exercise: 1 star, optional (plus_explicit_prop) *)
Definition P_plus_assoc (n m p: nat) : Prop :=
  n + (m + p) = (n + m) + p.

Definition plus_assoc''' : forall n m p : nat,
  P_plus_assoc n m p.
Proof.
  intros.
  apply nat_ind.
  - unfold P_plus_assoc. rewrite <- plus_n_O. rewrite <- plus_n_O. reflexivity.
  - intros. unfold P_plus_assoc in *. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite H. rewrite plus_n_Sm. reflexivity.
Qed.

Definition P_plus_comm (n m : nat) : Prop :=
  n + m = m + n.

Definition plus_comm''' : forall n m : nat,
  P_plus_comm n m.
Proof.
  intros.
  apply nat_ind.
  - unfold P_plus_comm. simpl. rewrite <- plus_n_O. reflexivity.
  - intros. unfold P_plus_comm in *. simpl. rewrite <- H. rewrite plus_n_Sm. reflexivity.
Qed.


(* Induction Principles in Prop *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Check ev_ind.

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - apply ev'_0.
  - intros m Hm IH. apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.























































