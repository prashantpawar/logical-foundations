Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Export ListNotations.

Require Import Perm.

From Hammer Require Import Hammer.


Notation "a >=? b" := (Nat.leb b a)
                        (at level 70, only parsing) : nat_scope.
Notation "a >? b" := (Nat.ltb b a)
                        (at level 70, only parsing) : nat_scope.
Notation " a =? b" := (beq_nat a b)
                        (at level 70) : nat_scope.

Fixpoint insert (i:nat) (l: list nat) :=
  match l with
  | nil => i::nil
  | h::t => if i <=? h then i::h::t else h :: insert i t
  end.

Fixpoint sort (l: list nat) :=
  match l with
  | nil => nil
  | h :: t => insert h (sort t)
  end.

Example sort_pi: sort [3;1;4;1;5;9;2;6;5;3;5]
                    = [1;1;2;3;3;4;5;5;5;6;9].
Proof. reflexivity. Qed.

Eval compute in insert 7 [1; 3; 4; 8; 12; 14; 18].

(* Specification of Correctness *)
Inductive sorted: list nat -> Prop :=
  | sorted_nil:
      sorted nil
  | sorted_l: forall x,
      sorted (x::nil)
  | sorted_cons: forall x y l,
      x <= y -> sorted (y::l) -> sorted (x::y::l).

Definition sorted' (al: list nat) :=
  forall i j,
  i < j < length al ->
  nth i al 0 <= nth j al 0.

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).



(* Proof of Correctness *)

(* Exercise: 3 stars (insert_perm) *)

Lemma insert_perm : forall x l,
  Permutation (x::l) (insert x l).
Proof.
  intros x l.
  rewrite Permutation_cons_append.
  induction l as [| a l]; auto.
  - simpl. bdestruct (x <=? a).
    + rewrite perm_swap. apply perm_skip.
    destruct l as [| b l]; auto.
    simpl. rewrite <- Permutation_cons_append.
    apply perm_swap.
    + apply perm_skip. auto.
Qed.

(* Exercise: 3 stars (sort_perm) *)
Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l.
  induction l as [| a l]; auto.
  simpl. rewrite <- insert_perm. apply perm_skip.
  apply IHl.
Qed.


(* Exercise: 4 stars (insert_sorted) *)
Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l E.
  generalize dependent a.
  induction l as [| b l]; intros.
  - simpl. apply sorted_l.
  - simpl. bdestruct (a <=? b).
    + simpl. apply sorted_cons; auto.
    + simpl.
Admitted.


(* Exercise: 2 stars (sort_sorted) *)
Theorem sort_sorted: forall l,
  sorted (sort l).
Proof.
  induction l.
  - apply sorted_nil.
  - simpl. apply insert_sorted. assumption.
Qed.

Theorem insertion_sort_correct:
  is_a_sorting_algorithm sort.
Proof.
  split.
  - (* LHS *) apply sort_perm.
  - (* RHS *) apply sort_sorted.
Qed.

(* Making Sure the Specification is Right *)

Lemma sorted'_nil : 
  sorted' [].
Proof.
  unfold sorted'.
  intros.
  simpl in *.
  inversion H. inversion H1.
Qed.

Lemma sorted'_l : forall x,
  sorted' (x::nil).
Proof.
  intros.
  unfold sorted'.
  intros.
  simpl in *.
  inversion H. inversion H1.
  - omega.
  - omega.
Qed.

Lemma sorted'_cons : forall x y l, 
  x <= y -> sorted' (y::l) -> sorted' (x::y::l).
Proof.
  unfold sorted'.
  intros. inversion H1. inversion H3.
  - hammer.






  intros.
  induction l.
  - unfold sorted'. intros. simpl in H1. inversion H1. inversion H3. subst.
    + inversion H2. subst. simpl; auto. subst. inversion H5.
    + subst. inversion H5. subst. inversion H2; subst. inversion H6.
  - unfold sorted'. intros. simpl in H1. 
    destruct (Datatypes.length l).
    + simpl. induction j.
      * inversion H1. inversion H2.
      * inversion H1.
      try (inversion H1);
      try (inversion H2).
    
    
    inversion H1. inversion H3; subst.
    + unfold sorted' in H0. simpl in H0.






  intros.
  generalize dependent x.
  generalize dependent y.
  induction l; intros.
  - unfold sorted'; intros. simpl in *. inversion H1. inversion H3; try (omega). rewrite H5 in H3.
    subst. inversion H2; try (omega).
  - unfold sorted'. unfold sorted' in H0. intros. simpl in *.
    inversion H1. inversion H3. subst.
    + Search nth. rewrite nth_overflow.





unfold sorted'; intros. simpl in *.
    inversion H1. inversion H3; subst.
    + apply lt_S_n in H3. apply lt_S_n in H3.
      
      destruct (Datatypes.length l).
      * unfold sorted' in H0. simpl in H0.
Admitted.



(* Exercise: 4 stars, optional (sorted_sorted') *)
Lemma sorted_sorted': forall al,
  sorted al -> sorted' al.
Proof.
  intros al E.
  induction al.
  - (* [] *) simpl. apply sorted'_nil.
  - (* (a :: al) *) induction al as [| b al].
    + apply sorted'_l.
    + apply sorted'_cons.
      * inversion E; subst; auto.
      * apply IHal. inversion E; subst; auto.
Qed.













































































































