Set Warnings "-notation-overridden,-parsing".
Require Export poly.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

(* Exercise 1 *)
(* there was a typo in the text *)
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1 H2.
  apply H1.
  apply H2.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  (* apply does simpl first *)
  apply H.
Qed.

(* Exercise 2 *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  Search rev.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with [c;d].
  assumption. assumption.
Qed.

Definition minustwo (n: nat): nat :=
  match n with
  | S (S n') => n'
  | _ => O
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p.
  intros H1 H2.
  apply trans_eq with m.
  apply H2. apply H1.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1.
  reflexivity.
Qed.


Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H.
  intro H1. apply H1.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* Exercise 3 *)
Example injection_ex3 : forall
  (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H0 H1.
  injection H1.
  intros _ H2.
  symmetry.
  apply H2.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - intros H.
    discriminate H.
Qed.

(* Exercise 4 *)
Example discriminate_ex3:
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof.
  intros X x y z l j.
  intro H.
  discriminate H.
Qed.

Theorem f_equal:
  forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

(* Exercise 5 *)
Theorem plus_n_n_injective:
  forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m H.
    simpl in H.
    destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - intros m H.
    simpl in H.
    destruct m as [| m'].
    + discriminate.
    + simpl in H.
      injection H as H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H.
      apply IH in H.
      apply f_equal.
      assumption.
Qed.

(* Exercise 6 *)
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n' IH].
  - intros m H.
    destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - intros m H.
    destruct m as [| m'].
    + discriminate.
    + simpl in H.
      apply IH in H.
      rewrite H.
      reflexivity.
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(* Exercise 7 *)
Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l H.
  generalize dependent l.
  induction n as [| n' IH].
  - intros l H.
    destruct l as [| a t].
    + reflexivity.
    + discriminate.
  - intros l H.
    destruct l as [| a t].
    + reflexivity.
    + simpl in H.
      injection H as H.
      apply IH in H.
      simpl.
      apply H.
Qed.

(*
  notes on unfold.
  simplication by simpl, apply, or reflexivity
  are usually somewhat conservative in the way
  that it will not unfold when it stuck on a
  conditional expression and cannot deduct the
  arguments without further infomation.
*)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity.
Qed.

(* Exercise 8 *)
Theorem combine_split:
  forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IH].
  - intros l1 l2 H.
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  - intros l1' l2' H.
    destruct h as [a b].
    simpl in H.
    destruct (split t) as [t1 t2].
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    rewrite -> IH.
    reflexivity.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:E1.
  - apply eqb_true in E1.
    rewrite -> E1.
    reflexivity.
  - destruct (n =? 5) eqn:E2.
    + apply eqb_true in E2.
      rewrite -> E2.
      reflexivity.
    + discriminate.
Qed.

(* Exercise 9 *)
Theorem bool_fn_applied_thrice:
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f true) eqn:Et.
  - destruct (f false) eqn:Ef.
    + destruct b eqn:Eb.
      * rewrite -> Et. rewrite -> Et. rewrite -> Et. reflexivity.
      * rewrite -> Ef. rewrite -> Et. rewrite -> Et. reflexivity.
    + destruct b eqn:Eb.
      * rewrite -> Et. rewrite -> Et. rewrite -> Et. reflexivity.
      * rewrite -> Ef. rewrite -> Ef. rewrite -> Ef. reflexivity.
  - destruct (f false) eqn:Ef.
    + destruct b eqn:Eb.
      * rewrite -> Et. rewrite -> Ef. rewrite -> Et. reflexivity.
      * rewrite -> Ef. rewrite -> Et. rewrite -> Ef. reflexivity.
    + destruct b eqn:Eb.
      * rewrite -> Et. rewrite -> Ef. rewrite -> Ef. reflexivity.
      * rewrite -> Ef. rewrite -> Ef. rewrite -> Ef. reflexivity.
Qed.

(* Exercise 10 *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intro n.
  induction n as [| n' IH].
  - intro m.
    destruct m as [| m'].
    + reflexivity.
    + reflexivity.
  - intro m.
    destruct m as [| m'].
    + reflexivity.
    + simpl. apply IH.
Qed.

(* Exercise 11 *)
Definition split_combine_statement: Prop :=
  forall (X Y: Type) (l: list (X * Y)) (l1: list X) (l2: list Y) ,
  combine l1 l2 = l ->
  length l1 = length l2 ->
  split l = (l1, l2).

Theorem split_combine: split_combine_statement.
Proof.
  intros X Y l.
  induction l as [| (a, b) t IH].
  - intros l1 l2 H1 H2.
    destruct l1.
    + destruct l2.
      * reflexivity.
      * discriminate.
    + destruct l2.
      * discriminate.
      * discriminate.
  - intros l1' l2' H1 H2.
    simpl.
    destruct (split t) as [t1 t2].
    destruct l1'.
    + discriminate.
    + destruct l2'.
      * discriminate.
      * simpl in H1.
        injection H1 as H1'1 H1'2 H1'3.
        simpl in H2.
        injection H2 as H2.
        pose (H3 := IH _ _ H1'3 H2).
        injection H3 as H3'1 H3'2.
        rewrite -> H3'1, H3'2.
        rewrite -> H1'1, H1'2.
        reflexivity.
Qed.

(* Exercise 12 *)
Theorem filter_exercise:
  forall (X : Type) (test : X -> bool)
         (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l.

  induction l as [| a t IH].
  - discriminate.
  - intros lf H.
    destruct (test a) eqn:E.
    + simpl in H.
      rewrite -> E in H.
      injection H as H'1 H'2.
      rewrite <- H'1.
      apply E.
    + simpl in H.
      rewrite -> E in H.
      apply (IH lf).
      apply H.
Qed.

(* Exercise 13 *)
Fixpoint forallb {X: Type} (f: X -> bool) (l: list X): bool :=
  match l with
  | [] => true
  | a :: t => f a && forallb f t
  end.

Fixpoint existsb {X: Type} (f: X -> bool) (l: list X): bool :=
  match l with
  | [] => false
  | a :: t => f a || existsb f t
  end.

Definition existsb' {X: Type} (f: X -> bool) (l: list X): bool :=
  negb (forallb (fun (x: X) => negb (f x)) l).

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb':
  forall (X: Type) (test: X -> bool) (l: list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [| a t IH].
  - reflexivity.
  - simpl. unfold existsb', forallb.
    destruct (test a) eqn: E.
    + reflexivity.
    + simpl. rewrite -> IH. reflexivity.
Qed.
