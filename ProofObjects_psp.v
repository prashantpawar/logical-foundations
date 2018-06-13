Set Warnings "-notation-overridden,-parsing".
Require Export IndProp.

Print ev.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.


(* Exercise: 2 stars (eight_is_even) *)
Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.

(* Programming with Tactics *)

Definition addl : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print addl.

Compute addl 2.

(* Logical Connectives as Inductive Types *)

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Print prod.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).


(* Exercise: 2 stars, optional (conj_fact) *)

Definition conj_fact : forall P Q R, 
  P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (HPQ : P /\ Q) (HQR : Q /\ R) =>
    match HPQ, HQR with
    | conj P Q1, conj Q2 R => conj P R
    end.

(* Disjunction *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

End Or.

(* Exercise: 2 stars, optional (or_commut'') *)

Definition or_comm' : forall P Q, P \/ Q -> Q \/ P.
Proof.
  intros P Q HPQ.
  destruct HPQ.
  - right. apply H.
  - left. apply H.
Qed.
Print or_comm'.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (HPQ: P \/ Q) =>
    match HPQ with
    | or_introl H => or_intror H
    | or_intror H => or_introl H
    end.

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercise: 2 stars, optional (ex_ev_Sn) *)
Definition ex_ev_Sn' : ex (fun n => ev (S n)).
Proof.
  exists 1.
  apply ev_SS.
  apply ev_0.
Qed.
Print ex_ev_Sn'.

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).


(* True and False *)

Inductive True : Prop :=
| I : True.

Inductive False : Prop :=.

End Props.

(* Equality *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                     (at level 70, no associativity)
                     : type_scope.

Check 2 = 2.

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] = x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

End MyEquality.

(* Exercise: 2 stars (equality_leibniz_equality) *)
Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x = y -> forall P:X->Prop, P x -> P y.
Proof.
  intros. rewrite <- H. apply H0.
Qed.

Lemma leibniz_equality__equality : forall (X : Type) (x y : X),
  (forall P:X->Prop, P x -> P y) -> x = y.
Proof.
  intros.
  apply H.
  reflexivity.
Qed.

































