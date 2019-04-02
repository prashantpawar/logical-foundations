Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Export ListNotations.
Require Export Permutation.

Check Nat.lt.
Check lt.
Goal Nat.lt = lt.
Proof. reflexivity. Qed.
Check Nat.ltb.
Locate "_ < _".
Locate "<?".

Check Nat.ltb_lt.

Notation "a >=? b" := (Nat.leb b a)
                        (at level 70, only parsing) : nat_scope.
Notation "a >? b" := (Nat.ltb b a)
                        (at level 70, only parsing) : nat_scope.
Notation " a =? b" := (beq_nat a b)
                        (at level 70) : nat_scope.

Print reflect.

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt. 
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Example reflect_example1: forall a, (if a <?5 then a else 2) < 6.
Proof.
  intros a.
  destruct (blt_reflect a 5) as [H|H].
  - omega.
  - apply not_lt in H. omega.
Qed.


(* Some advanced tactical hacking *)

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in 
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
      [ | try first [apply not_lt in H | apply not_le in H]
      ]
    ].

Example reflect_example2: forall a, (if a<?5 then a else 2) < 6. 
Proof.
  intros.
  bdestruct (a <? 5); omega.
Qed.

Ltac inv H := inversion H; clear H; subst.

(* Linear Integer Inequalities *)
Module Exploration1.

Theorem omega_example1:
  forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
    k > i.
Proof.
  intros.
  Search (~ _ <= _ -> _).
  apply not_le in H0.
  Search (_ > _ -> _ > _ -> _ > _).
  apply gt_trans with j.
  apply gt_trans with (k - 3).
Abort.

Theorem bogus_substraction: ~ (forall k:nat, k > k - 3).
Proof.
  intro.
  specialize (H O).
  simpl in H. inversion H.
Qed.

Theorem omega_example1:
  forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
    k > i.
Proof.
  intros.
  apply not_le in H0.
  unfold gt in H0.
  unfold gt.
  Search (_ < _ -> _ <= _ -> _ < _).
  apply lt_le_trans with j.
  - apply H.
  - apply le_trans with (k - 3).
    + Search (_ < _ -> _ <= _). apply lt_le_weak. apply H0.
    + apply le_minus.
Qed.

Theorem omega_example2:
  forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
    k > i.
Proof.
  intros.
  omega.
Qed.

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b::a::ar else a::b::ar
  | _ => al
  end.

Example maybe_swap_123:
  maybe_swap [1; 2; 3] = [1; 2; 3].
Proof.
  reflexivity.
Qed.

Example maybe_swap_321:
  maybe_swap [3; 2; 1] = [2; 3; 1].
Proof.
  reflexivity.
Qed.

Check (1>2).
Check (1>?2).

Locate ">?".

Print Nat.ltb.
Locate ">=?".

Locate leb.
Print leb.
Print Nat.leb.

Theorem maybe_swap_idempotent:
  forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros.
  destruct al as [| a al].
  - reflexivity.
  - destruct al as [| b al].
    + reflexivity.
    + simpl. bdestruct (b <? a).
      * simpl. bdestruct (a <? b); auto.
        rewrite H in H0. 
        try omega.
      * simpl. bdestruct (b <? a); auto.
        unfold ge in H. omega.
Abort.

Theorem maybe_swap_idempotent:
  forall al, maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros.
  destruct al as [ | a al]; auto.
  - destruct al as [ | b al]; auto. simpl.
    destruct (blt_reflect b a).
    + simpl.
    (* destruct (blt_reflect a b). *) 
    bdestruct (b <? a).
      * simpl. bdestruct (a <? b).
        omega. reflexivity. 
      * simpl. bdestruct (a <? b).
        omega. reflexivity.
    + simpl.
      bdestruct (b <? a). omega. reflexivity.
Qed.

(* Permutations *)

Locate Permutation.
Check Permutation.

Print Permutation.

(* Exercise: 2 stars (Permutation properties) *)

(*
1. If Permutation al bl, then length al = length bl.
2. If Permutation al bl, then Permutation bl al.
3. [1;1] is NOT a permutation of [1;2].
4. [1;2;3;4] IS a permutation of [3;4;2;1].
5. If Permutation al bl and cl subset of al then exists dl for which Permutation cl dl and dl subset of bl.
6. If x is an element of al /\ Permutation al bl then x is an element of bl.
7. If x is an element of al /\ x is not an element of bl then ~( Permutation al bl)
8. If al + bl = cl /\ Permutation al al' /\ Permutation bl bl' /\ al' + bl' = cl' then Permutation cl cl'.

*)

Search Permutation.


Example butterfly: forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r] ++ [f;l;y]) ([f;l;u;t;t;e;r] ++ [b;y]).
Proof.
  intros.
  change [b;u;t;t;e;r] with ([b] ++ [u;t;t;e;r]).
  change [f;l;u;t;t;e;r] with ([f;l] ++ [u;t;t;e;r]).
  remember [u;t;t;e;r] as utter.
  clear Hequtter.
  rewrite <- app_assoc. rewrite <- app_assoc.
  apply perm_trans with (utter ++ [f; l; y] ++ [b]).
  - rewrite (app_assoc utter [f;l;y]).
    apply Permutation_app_comm.
  - eapply perm_trans.
    2: apply Permutation_app_comm.
      rewrite <- app_assoc.
   Search (Permutation (_ ++ _)  (_ ++ _)).
    apply Permutation_app_head.
    eapply perm_trans.
    2: apply Permutation_app_comm. simpl.
    Check perm_skip.
    apply perm_skip. apply perm_skip.
    apply perm_swap.
Qed.

(* Exercise: 3 stars (permut_example) *)
Check perm_skip.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.

Example permut_example: forall (a b: list nat),
  Permutation (5::6::a++b) ((5::b)++(6::a++[])).
Proof.
  intros.
  simpl.
  apply perm_skip.
  rewrite <- app_nil_end.
  rewrite app_comm_cons.
  apply Permutation_app_comm.
Qed.

(* Exercise: 1 star (not_a_permutation) *)

Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Example not_a_permutation:
  ~ Permutation [1;1] [1;2].
Proof.
  unfold not.
  intros.
  change [1; 1] with ([1] ++ [1]) in H.
  change [1; 2] with ([1] ++ [2]) in H.
  apply Permutation_app_inv_l in H.
  apply Permutation_length_1_inv in H.
  inversion H.
Qed.


Theorem maybe_swap_perm : forall al,
  Permutation al (maybe_swap al).
Proof.
  intros al.
  destruct al as [| a al].
  - auto.
  - destruct al as [| b al].
    + auto.
    + simpl. bdestruct (b <? a).
      * apply perm_swap.
      * reflexivity.
Qed.


Definition first_le_second (al: list nat) : Prop :=
  match al with
  | a::b::_ => a <= b
  | _ => True
  end.


Theorem maybe_swap_correct: forall al,
  Permutation al (maybe_swap al)
  /\ first_le_second (maybe_swap al).
Proof.
  intros al.
  split.
  - apply maybe_swap_perm.
  - destruct al as [| a al].
    + simpl. auto.
    + destruct al as [| b al].
      * simpl. auto.
      * simpl. bdestruct (b <? a); auto.
        simpl. apply Nat.lt_le_incl. auto.
Qed.

End Exploration1.

(* Summary: Comparisons and Permutations *)

(* Exercise: 2 stars (Forall_perm) *)
Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  intros A f al bl H1 H2.
  induction H1; auto.
  - apply Forall_cons.
    + inversion H2; subst; auto.
    + apply IHPermutation. inversion H2; subst; auto.
  - inversion H2; subst. inversion H3; subst.
    inversion H5; auto.
Qed.






























