Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.
Require Export Lists.


Check 3 = 3.

Check forall n m : nat, n + m = m + n.

Check 2 = 2.

Check forall n : nat, n = 2.

Check 3 = 4.


Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof.
  reflexivity.
Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof.
  reflexivity.
Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.

Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop,
  A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 2 stars (and_exercise) *)
Example and_exercise_firsttry :
  forall n m : nat,
  n + m = 0 ->
  n = 0 /\ m = 0.
Proof.
  intros n m H.
  induction n, m.
  - auto.
  - auto.
  - split.
    + simpl in H. rewrite <- plus_n_O in H. apply H.
    + auto.
  - inversion H.
Qed.

Example and_exercise :
  forall n m : nat,
  n + m = 0 ->
  n = 0 /\ m = 0.
Proof.
  intros n m H.
  induction n.
  - auto.
  - inversion H.
Qed.


Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 ->
  n + m = 0.
Proof.
  intros.
  destruct H as [Hn Hm].
  rewrite Hn. apply Hm.
Qed.

Lemma and_example2' : forall n m : nat,
  n = 0 ->
  m = 0 ->
  n + m = 0.
Proof.
  intros.
  rewrite H. apply H0.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 ->
  n * m = 0.
Proof.
  intros.
  assert (H' : n = 0 /\ m = 0).
  { induction n.
    - auto.
    - inversion H.
  }
  destruct H' as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.


Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.


(* Exercise: 1 star, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

(* Exercise: 2 stars (and_assoc) *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check and.


Lemma or_example : forall n m : nat,
  n = 0 \/ m = 0 ->
  n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on 
    n = 0 \/ m = 0 *)
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.


Lemma or_intro : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros.
  induction n.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  generalize dependent n.
  induction n.
  - intros Hm. left. reflexivity.
  - intros Hnm. induction m.
    + right. reflexivity.
    + left. inversion Hnm.
Qed.


(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quadlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(* Exercise: 2 stars, optional (not_implies_our_not) *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra.
  inversion contra.
Qed.

Check (0 <> 1).

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything: forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P HP.
  unfold not.
  intros G.
  apply G.
  apply HP.
Qed.

(* Exercise: 2 stars, recommended (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HQ HP.
  unfold not in HQ.
  apply HQ.
  apply HPQ.
  apply HP.
Qed.

(* Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P [HP HNP].
  apply HNP.
  apply HP.
Qed.


Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - apply ex_falso_quadlibet. unfold not in H. apply H. reflexivity.
  - reflexivity.
Qed.


Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity)
                        : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HP HQ].
  unfold iff.
  split.
  - apply HQ.
  - apply HP.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros.
  unfold iff.
  split.
  - intros H. induction b. 
    + exfalso. apply H. reflexivity.
    + reflexivity.
  - intros H. induction b.
    + inversion H.
    + unfold not. intros H'. inversion H'.
Qed.

Lemma or_intro_2 : forall A B : Prop,
  B -> A \/ B.
Proof.
  intros A B HB.
  right.
  apply HB.
Qed.

(* Exercise: 3 stars (or_distributes_over_and) *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ HR]].
    + split.
      { - left. apply HP. }
      { - left. apply HP. }
    + split.
      { - right. apply HQ. }
      { - right. apply HR. }
  - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right. split.
      { - apply HQ. }
      { - apply HR. }
Qed.


Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma mult_0 : forall n m, 
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc : forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc. reflexivity.
Qed.

Lemma apply_iff_example : forall n m : nat,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  apply mult_0.
Qed.


Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(* Exercise: 1 star, recommend (dist_not_exists). *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros.
  destruct H0.
  apply H0.
  apply H.
Qed.

(* Exercise: 2 stars (dist_exists_or) *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  - intros [x [HP | HQ]].
    + left. exists (x). apply HP.
    + right. exists (x). apply HQ.
  - intros [[x HP] | [x HQ]]. 
    + exists (x). left. apply HP.
    + exists (x). right. apply HQ.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2:
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros. induction l.
  - apply H.
  - simpl. destruct H as [Hx | ].
    + left. rewrite Hx. reflexivity.
    + right. apply IHl. apply H.
Qed. 

(* Exercise: 2 stars (In_map_iff) *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - intros H. induction l.
      { - inversion H. }
      { - simpl. simpl in H. induction H as [Hx | E].
          + exists (x). split.
            * apply Hx.
            * left. reflexivity.
          + apply IHl in E. destruct E as [x' H1]. 
            exists (x'). split. 
            * apply H1.
            * right. apply H1.
       }
   - intros [x H]. induction l.
    + destruct H. apply H0. 
    + simpl. simpl in H. destruct H as [Hfx [Hx0 | Hxl]].
      * left. rewrite <- Hx0 in Hfx. apply Hfx.
      * right. apply IHl. split.
        { - apply Hfx. }
        { - apply Hxl. }
Qed.

Lemma app_r_nil : forall X (l : list X),
  [] ++ l = l.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl. reflexivity.
Qed.


(* Exercise: 2 stars (In_app_iff) *)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
  - intros H. induction l.
    + simpl in H. right. apply H.
    + simpl in H. destruct H as [Hx | Ha].
      * simpl. left. left. apply Hx.
      * apply IHl in Ha. destruct Ha.
        { - simpl. left. right. apply H. }
        { - right. apply H. }
  - intros H. induction l.
    + simpl. destruct H.
      * induction H.
      * apply H.
    + destruct H as [H1 | H2].
      * simpl. simpl in H1. destruct H1.
        { - left. apply H. }
        { - right. apply IHl. left. apply H. }
      * simpl. right. apply IHl. right. apply H2.
Qed.

(* Exercise: 3 stars, recommended (All) *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: l' => P x /\ All P l'
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  - intros H. induction l.
    + simpl. apply I.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl. intros. apply H. simpl. right. apply H0.
  - intros. induction l.
    + destruct H0.
    + simpl in H. simpl in H0. 
      destruct H. destruct H0.
        * rewrite H0 in H. apply H.
        * apply IHl in H1.
          { - apply H1. }
          { - apply H0. }
Qed.

(* Exercise: 3 stars (combine_odd_even) *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  := fun (n : nat) =>
      match (oddb n) with
      | true => Podd n
      | false => Peven n
      end.

Lemma oddb_S : forall n,
  oddb (S n) = negb (oddb n).
Proof.
  intros. induction n.
  - simpl. reflexivity.
  - rewrite IHn. rewrite negb_involutive. reflexivity.
Qed.


Theorem not_true_is_false'' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
         (oddb n = true -> Podd n) ->
         (oddb n = false -> Peven n) ->
         combine_odd_even Podd Peven n.
Proof.
  intros.
  induction n.
  - unfold combine_odd_even. simpl. apply H0. reflexivity.
  - unfold combine_odd_even. destruct (oddb (S n)). 
      * apply H. reflexivity.
      * apply H0. reflexivity. 
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H. destruct (oddb n).
  - apply H.
  - inversion H0.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H. destruct (oddb n).
  - inversion H0.
  - apply H.
Qed.

Check plus_comm.

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros. rewrite plus_comm.
  assert (H: y + z = z + y).
  { - apply plus_comm. }
  rewrite H. reflexivity.
Qed.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros. 
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.


Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
          as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

Axiom function_extensionality : forall {X Y: Type}
                                       {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply function_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

(* Exercise: 4 stars (tr_rev_correct) *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Compute app [1;2;3] [4;5;6].

Compute rev_append [1;2;3] [4;5;6].

Compute tr_rev [1;2;3].

Lemma rev_append_aux : forall X (l1 l2 : list X),
  rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  induction l1.
  - reflexivity.
  - intros l2. simpl. 
    rewrite (IHl1 ([x])).
    rewrite (IHl1 (x::l2)).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros.
  apply function_extensionality. induction x.
  - reflexivity.
  - unfold tr_rev. simpl. rewrite rev_append_aux. unfold tr_rev in IHx. rewrite IHx. reflexivity.
Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k.
  induction k.
  - reflexivity.
  - simpl. apply IHk.
Qed.

(*Exercise: 3 stars (evenb_double_conv) *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                  else S (double k).
Proof.
  intros.
  induction n.
  - exists 0. reflexivity.
  - rewrite evenb_S. destruct IHn.
    destruct (evenb n).
    + simpl. exists x. rewrite <- H. reflexivity.
    + exists (S x). simpl. rewrite <- H. reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n.
  split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    exists k. rewrite H in Hk. apply Hk.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros. split.
  - intros H. apply beq_nat_true. apply H.  
  - intros H. rewrite H. symmetry. apply beq_nat_refl.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

Example even_1000 : exists k, 1000 = double k.
Proof.
  exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(* Exercise: 2 stars (logical_connectives) *)
Lemma andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  split.
  - intros H. split.
    + destruct b1.
      * reflexivity.
      * destruct H. unfold andb. reflexivity.
    + destruct b2.
      * reflexivity.
      * destruct H. unfold andb. destruct b1.
        { - reflexivity. }
        { - reflexivity. }
  - intros [H1 H2]. rewrite H1. apply H2.
Qed.


Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  split.
  - intros H. rewrite <- H. unfold orb. destruct b1.
    + left. reflexivity.
    + right. reflexivity.
  - intros [H1 | H2].
    + rewrite H1. reflexivity.
    + rewrite H2. destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

Require Import NArith.

(* Exercise: 1 star (beq_nat_false_iff) *)
Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  intros x y.
  split.
  - unfold not. intros H G. rewrite <- G in H.
    rewrite <- beq_nat_refl in H. inversion H.
  - unfold not. intros. destruct (beq_nat x y) eqn:G.
    + exfalso. apply beq_nat_true in G. apply H. apply G.
    + reflexivity.
Qed.

(* Exercise: 3 stars (beq_list) *)
Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => beq x y && beq_list beq l1' l2'
  | _, _ => false
  end.

Theorem beq_list_true_iff' :
  forall (A : Type) (beq : A -> A -> bool), (
    forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
      forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq h1.
  induction l1 as [|a l1].
  + induction l2 as [|b l2].
    - split; reflexivity.
    - split; intros h2; inversion h2.
  + induction l2 as [|b l2].
    - split; inversion 1.
    - simpl; split.
      * intros h2.
        apply andb_true_iff in h2.
        destruct h2 as [h2 h3].
        apply h1 in h2.
        apply IHl1 in h3.
        rewrite h2; rewrite h3; reflexivity.
      * intros h2.
        apply andb_true_iff.
        injection h2 as h2 h3.
        rewrite h2; rewrite <- h3.
        split; [apply h1 | apply IHl1]; reflexivity.
Qed.

Lemma list_body_eq : forall X (x:X) (l1 l2 : list X),
  x :: l1 = x :: l2 ->
  l1 = l2.
Proof.
  intros.
  induction l1, l2.
  - reflexivity.
  - inversion H.
  - inversion H.
  - inversion H. rewrite <- H2. reflexivity.
Qed.

Lemma list_body_eq_inv : forall X (x:X) (l1 l2 : list X),
  l1 = l2 ->
  x :: l1 = x :: l2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H.
  induction l1 as [| x l1'], l2 as [| y l2'].
  - simpl. split.
    + reflexivity.
    + reflexivity.
  - simpl. split.
    + intros G. inversion G.
    + intros G. inversion G.
  - simpl. split.
    + intros G. inversion G.
    + intros G. inversion G.
  - simpl. split.
    + intros G. rewrite andb_true_iff in G.
      destruct G. apply IHl1' in H1. apply H in H0. 
      rewrite H0. rewrite H1. reflexivity.
    + intros G. rewrite andb_true_iff. split.
      * inversion G. apply H. reflexivity.
      * inversion G. apply IHl1' in H2. 
        inversion G. rewrite H4 in H2. apply H2.
Qed.









































