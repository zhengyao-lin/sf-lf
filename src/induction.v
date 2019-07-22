Require Export basics.

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n.
  induction n as [| n' IH].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IH. reflexivity.
Qed.

Theorem minus_diag : forall n : nat,
  minus n n = 0.
Proof.
  (* optional - intros n. *)
  induction n as [| n' IH].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IH. reflexivity.
Qed.

(* Exercise 1 *)
Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IH].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IH].
  - simpl. rewrite <- (plus_n_O m). reflexivity.
  - simpl. rewrite -> IH. rewrite -> (plus_n_Sm m n'). reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

(* Exercise 2 *)
Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> (plus_comm n' (S n')).
    simpl. rewrite -> IH.
    reflexivity.
Qed.

(* Exercise 3 *)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - rewrite -> IH. simpl.
    assert (H: forall b : bool, negb (negb b) = b). {
      destruct b.
      - reflexivity.
      - reflexivity.
    }
    rewrite -> (H (evenb n')).
    reflexivity.
Qed.
