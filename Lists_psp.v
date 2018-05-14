(* [Case] is not built into Coq: we need to define it ourselves.
    There is no need to understand how it works -- you can just skip
    over the definition to the example that follows.  It uses some
    facilities of Coq that we have not discussed -- the string
    library (just for the concrete syntax of quoted strings) and the
    [Ltac] command, which allows us to declare custom tactics.  Kudos
    to Aaron Bohannon for this nice hack! *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require Export Induction.

(*
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
*)

(** * Lists: Working with Structured Data *)
Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Example test_fst_1: (fst (pair 3 5)) = 3.
Proof. simpl. reflexivity. Qed.

Example test_snd_1: (snd (pair 2 4)) = 4.
Proof. simpl. reflexivity. Qed.

Notation "( x , y )" := (pair x y).

Compute (fst (3, 4)).

Definition fst' (p: natprod) : nat :=
  match p with
  | (x, y) => x
  end.

Definition snd' (p: natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Definition swap_pair (p: natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Compute (swap_pair (3, 5)).

Theorem surjective_pairing' : forall (n m:nat),
  (n,m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.


Theorem snd_fst_is_swap : forall(p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute (repeat 2 3).

Fixpoint length (n : natlist) : nat :=
  match n with
  | nil => 0
  | h :: t => plus 1 (length t)
  end.

Compute (length [1;2;3]).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app_1: [1;2;3] ++ [4;5;6] = [1;2;3;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_app_2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app_3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Fixpoint tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeroes (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeroes t
  | h :: t => h :: (nonzeroes t)
  end.

Example test_nonzeroes: nonzeroes [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
    match (evenb h) with
    | true => oddmembers t
    | false => h :: (oddmembers t)
    end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 =>
    match l2 with
    | nil => l1
    | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
    end
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
    match (beq_nat h v) with
    | true => plus 1 (count v t)
    | false => (count v t)
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.


Definition sum : bag -> bag -> bag :=
  alternate.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat 0 (count v s)).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => 
    match (beq_nat h v) with
    | true => t
    | false => h :: remove_one v t
    end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match (beq_nat h v) with
    | true => remove_all v t
    | false => h :: (remove_all v t)
    end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h1 :: t1 =>
    match leb (count h1 s1) (count h1 s2) with
    | false => false
    | true => (subset t1 s2)
    end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.


Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(** Induction on Lists **)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = const n l' *)
    simpl. rewrite <- IHl'.
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
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

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> app_length, plus_comm. 
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(* List Exercises, Part 1 *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite -> plus_comm. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    rewrite -> app_nil_r. reflexivity. 
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite? app_assoc. reflexivity.
Qed.  

Lemma nonzeros_app: forall l1 l2 : natlist,
  nonzeroes (l1 ++ l2) = (nonzeroes l1) ++ (nonzeroes l2).
Proof.
  intros l1 l2. induction l1.
  Case "l1 = []". reflexivity.
  Case "l1 = n :: l1'".
    destruct n.
    - simpl. rewrite -> IHl1. reflexivity.
    - simpl. rewrite -> IHl1. reflexivity.
Qed.

(* Exercise: 2 stars (beq_natlist) *)
Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
           | nil => true
           | _ => false
           end
  | n1 :: t1 => match l2 with
                | nil => false
                | n2 :: t2 => 
                    andb (beq_nat n1 n2) (beq_natlist t1 t2)
                end
  end.

Example test_beq_natlist1: 
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2:
  (beq_natlist [1;2;3] [1;2;3] = true).
Proof. reflexivity. Qed.

Example test_beq_natlist3:
  (beq_natlist [1;2;3] [1;2;4] = false).
Proof. reflexivity. Qed.


Theorem beq_nat_refl : forall n:nat,
  true = beq_nat n n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l.
  Case "l = []". reflexivity.
  Case "l = n :: l'". 
    simpl. rewrite <- IHl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s.
  Case "s = []". reflexivity.
  Case "s = n :: s'". simpl. reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n.
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem remove_decrease_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s.
  Case "s = []". reflexivity.
  Case "s = n :: s'".
    destruct n.
    - simpl. rewrite -> ble_n_Sn. reflexivity.
    - simpl. rewrite -> IHs. reflexivity.
Qed.

Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H. induction l1 as [| n1 l1' IHl1].
  - rewrite <- rev_involutive. rewrite <- H. reflexivity.
  - rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
Qed.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42 (* arbitrary *)
  | a :: l' => match beq_nat n O with
              | true => a
              | false => nth_bad l' (pred n)
              end
  end.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Compute nth_bad [1;2;3] 1.
Compute nth_bad [1;3;4] 10.
Compute nth_error [1;2;3;4] 3.
Compute nth_error [1;2;3;4] 10.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1: hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2: hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3: hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. destruct l.
  Case "l = []". reflexivity.
  Case "l = n :: l'". reflexivity.
Qed.

End NatList.

Export NatList.

(* Partial Maps *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, 
  true = beq_id x x.
Proof.
  intros x. destruct x.
  simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

Definition update (d: partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x: id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v : nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v. induction d.
  - simpl. rewrite <- beq_id_refl. reflexivity.
  - simpl. rewrite <- beq_id_refl. reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x : id) (v : nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v. induction d.
  - simpl. rewrite <- beq_id_refl. reflexivity.
  - simpl. rewrite <- beq_id_refl. reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.


Check baz.

End PartialMap.






























