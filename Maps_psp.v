Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : forall s : string,
  true = beq_string s s.
Proof.
  intros. unfold beq_string.
  destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
  split.
  - intros. unfold beq_string in H. destruct (string_dec x y) as [|Hs].
    + apply e.
    + inversion H.
  - intros. rewrite H. rewrite beq_string_refl with y. reflexivity.
Qed.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity. 
Qed.

Theorem false_beq_string : forall x y : string,
  x <> y -> beq_string x y = false.
Proof.
  intros x y. rewrite beq_string_false_iff.
  intros H. apply H.
Qed.

Definition total_map (A:Type) := string -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                             (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.


Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
            "bar" true.

Notation "{ --> d }" := (t_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).


Definition examplemap' :=
  { --> false } & { "foo" --> true ; "bar" --> true }.

(* Exercise: 1 star, optional (t_apply_empty) *)
Lemma t_apply_empty: forall (A:Type) (x: string) (v: A),
  { --> v } x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.

(* Exercise: 2 stars, optional (t_update_eq) *)
Lemma t_update_eq: forall A (m: total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  intros.
  unfold t_update. rewrite <- beq_string_refl. reflexivity.
Qed.

(* Exercise: 2 stars, optional (t_update_neq) *)
Theorem t_update_neq : forall (X:Type) v x1 x2
                              (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros.
  unfold t_update. rewrite false_beq_string.
  - reflexivity.
  - apply H.
Qed.

(* Exercise: 2 stars, optional (t_update_shadow) *)
Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
  m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (beq_string x x0).
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: 2 stars, optional (beq_stringP) *)
Lemma beq_stringP : forall x y,
  reflect (x = y) (beq_string x y).
Proof.
  intros.
  destruct (beq_string x y) eqn:H.
  - apply ReflectT. unfold beq_string in H. destruct (string_dec x y).
    + apply e.
    + inversion H.
  - apply ReflectF. rewrite <- beq_string_false_iff. apply H.
Qed.

(* Exercise: 2 stars (t_update_same) *)
Theorem t_update_same : forall X x (m : total_map X),
  m & { x --> m x } = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (beq_stringP x x0).
  - rewrite e. reflexivity.
  - reflexivity.
Qed.

(* Exercise: 3 stars, recommended (t_update_permute) *)
Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                                  (m : total_map X),
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  = m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (beq_stringP x2 x) as [H1 | H1].
  - destruct (beq_stringP x1 x) as [H2 | H2].
    + unfold not in H. destruct H. rewrite H1. rewrite H2. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(* Partial Maps *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                    (x : string) (v : A) :=
  m & { x --> (Some v) }.

Notation "m '&' {{ a --> x }}" := 
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" := 
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" := 
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z }}) d t) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t }}) e u) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}) f v) (at level 20).

Lemma apply_empty : forall (A: Type) (x: string), @empty A x = None.
Proof.
  intros.
  unfold empty. unfold t_empty. reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (m & {{ x --> v }}) x = Some v.
Proof.
  intros.
  unfold update.
  rewrite t_update_eq.
  reflexivity.
Qed.

Lemma update_neg : forall (X:Type) v x1 x2
                          ( m: partial_map X),
  x2 <> x1 ->
  (m & {{ x2 --> v }}) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update.
  apply t_update_neq. apply H.
Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  m & {{ x --> v1 ; x --> v2 }} = m & {{x --> v2}}.
Proof.
  intros.
  unfold update.
  apply t_update_shadow.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  m & {{x --> v}} = m.
Proof.
  intros.
  unfold update.
  rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                          (m : partial_map X),
  x2 <> x1 ->
  m & {{x2 --> v2 ; x1 --> v1}}
  = m & {{x1 --> v1 ; x2 --> v2}}.
Proof.
  intros.
  apply t_update_permute.
  apply H.
Qed.



































