Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise 1 *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise 2 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

(* Exercise 3 *)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(* Exercise 4 *)
Definition ltb (n m : nat) : bool :=
    andb (n <=? m) (negb (n =? m)).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Proof. reflexivity. Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. reflexivity. Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. reflexivity. Qed.

(* Exercise 5 *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H_1 H_2.
  rewrite -> H_1.
  rewrite -> H_2.
  reflexivity.
Qed.

(* Exercise 6 *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

(* Exercise 7 *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c.
    - reflexivity.
    - rewrite <- H.
      destruct b.
      + reflexivity.
      + reflexivity.
Qed.

(* Exercise 8 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise 9 *)
(* example:
Fixpoint diverged (n : nat) : nat :=
  match n with
  | O => diverged (S O)
  | S n' => O
  end.
*)

(* Exercise 10 *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros f_is_id.
  intros b.
  rewrite -> f_is_id.
  rewrite -> f_is_id.
  reflexivity.
Qed.

(* Exercise 11 *)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros f_is_id.
  intros b.
  rewrite -> f_is_id.
  rewrite -> f_is_id.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise 12 *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b.
  - destruct c.
    + reflexivity.
    + simpl in H.
      rewrite -> H.
      reflexivity.
  - destruct c.
    + simpl in H.
      rewrite -> H.
      reflexivity.
    + reflexivity.
Qed.

(* Exercise 13 *)
Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (n : bin) : bin :=
  match n with
  | Z    => B Z
  | A n' => B n'
  | B n' => A (incr n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | Z => O
  | A n' => (bin_to_nat n') * 2
  | B n' => (bin_to_nat n') * 2 + 1
  end.

Example test_bin_incr1 : incr Z = B Z.
Proof. reflexivity. Qed.
Example test_bin_incr2 : incr (A (B (B Z))) = B (B (B Z)).
Proof. reflexivity. Qed.
Example test_bin_incr3 : incr (B (B (B Z))) = A (A (A (B Z))).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat Z = 0.
Proof. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (B (B (B Z))) = 7.
Proof. reflexivity. Qed.
