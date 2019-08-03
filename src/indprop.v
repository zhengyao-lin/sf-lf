Set Warnings "-notation-overridden,-parsing".
Require Export logic.
Require Coq.omega.Omega.

Inductive even: nat -> Prop :=
  | ev_0: even 0
  | ev_SS (n: nat) (H: even n): even (S (S n)).

Theorem ev_plus4: forall n, even n -> even (4 + n).
Proof.
  intros n Hn.
  apply ev_SS.
  apply ev_SS.
  apply Hn.
Qed.

(* Exercise 1 *)
Theorem ev_double: forall n,
  even (double n).
Proof.
  intros n.
  induction n as [| n' IH].
  - apply ev_0.
  - simpl. apply ev_SS.
    apply IH.
Qed.

Theorem ev_inversion:
  forall (n: nat),
    even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n H.
  destruct H as [| n0 H'].
  - left. reflexivity.
  - right. exists n0. split. reflexivity. apply H'.
Qed.

Theorem ev_minus2: forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n H.
  destruct H as [| n' H].
  - apply ev_0.
  - apply H.
Qed.

Theorem evSS_ev: forall n,
  even (S (S n)) -> even n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H.
  - discriminate.
  - destruct H as [n' [H1 H2]].
    + injection H1 as H1.
      rewrite <- H1 in H2.
      apply H2.
Qed.

Theorem evSS_ev': forall n,
  even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H as [| n' H'].
  apply H'.
Qed.

(* Exercise 2 *)
Theorem SSSSev__even: forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  inversion H as [| n' H1 H2].
  inversion H1 as [| n'' H3 H4].
  apply H3.
Qed.

(* Exercise 3 *)
Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem inversion_ex1: forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Lemma ev_even: forall n,
  even n -> exists k, n = double k.
Proof.
  intros n H.
  induction H as [| n' H' [k' IH]].
  - exists 0. reflexivity.
  - exists (S k').
    simpl. apply f_equal. apply f_equal. apply IH.
Qed.

Theorem ev_even_iff: forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(* Exercise 4 *)
Theorem ev_sum:
  forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m H1 H2.
  induction H1 as [| n' H1' IH].
  - apply H2.
  - apply ev_SS. apply IH.
Qed.

(* Exercise 5 *)
Inductive even': nat -> Prop :=
  | even'_0: even' 0
  | even'_2: even' 2
  | even'_sum n m (Hn : even' n) (Hm : even' m): even' (n + m).

Theorem even'_ev: forall n, even' n <-> even n.
Proof.
  intros n. split.
  - intros H1.
    induction H1 as [| | n' m' Hn' IH1 Hm' IH2].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IH1.
      * apply IH2.
  - intros H1.
    induction H1 as [| n' Hn' IH].
    + apply even'_0.
    + assert (H: S (S n') = 2 + n').
      { reflexivity. }
      rewrite H.
      apply even'_sum.
      * apply even'_2.
      * apply IH.
Qed.

(* Exercise 6 *)
Theorem ev_ev__ev: forall n m,
  even (n + m) -> even n -> even m.
Proof.
  intros n m Hnm Hn.
  induction Hn as [| n' Hn' IH].
  - apply Hnm.
  - simpl in Hnm. apply evSS_ev in Hnm.
    apply IH. apply Hnm.
Qed.

(* Exercise 7 *)
Theorem ev_plus_plus: forall n m p,
  even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros n m p.
  intros Hnm Hnp.
  assert (H := ev_sum (n + m) (n + p) Hnm Hnp).
  rewrite plus_assoc in H.
  rewrite (plus_comm (n + m) n) in H.
  rewrite plus_assoc in H.
  rewrite <- double_plus in H.
  rewrite <- plus_assoc in H.
  assert (H1 := ev_double n).
  apply (ev_ev__ev (double n) (m + p)).
  apply H. apply H1.
Qed.

Inductive le: nat -> nat -> Prop :=
  | le_n n: le n n
  | le_S n m (H: le n m): le n (S m).

Notation "m <= n" := (le m n).

Definition lt (n m: nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of: nat -> nat -> Prop :=
  | sq n: square_of n (n * n).

Inductive next_nat: nat -> nat -> Prop :=
  | nn n: next_nat n (S n).

Inductive next_even: nat -> nat -> Prop :=
  | ne_1 n: even (S n) -> next_even n (S n)
  | ne_2 n (H: even (S (S n))): next_even n (S (S n)).

(* Exercise 8 *)
Definition total_relation (n m: nat) := n <= m \/ m <= n.

(* Exercise 9 *)
Definition empty_relation (n m: nat) := n < m /\ m < n.

(* Exercise 10 *)
Lemma le_trans:
  forall m n o,
    m <= n -> n <= o -> m <= o.
Proof.
  intros m n o.
  intros Hmn Hno.

  induction Hno as [o' | n' o' H' IH].
  - apply Hmn.
  - apply le_S.
    apply IH.
    apply Hmn.
Qed.

Theorem O_le_n:
  forall n, 0 <= n.
Proof.
  intros n.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem n_le_m__Sn_le_Sm:
  forall n m,
    n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m:
  forall n m,
    S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - assert (H': n <= S n). { apply le_S. apply le_n. }
    apply (le_trans n (S n) m H').
    apply H2.
Qed.

Theorem le_plus_l:
  forall a b, a <= a + b.
Proof.
  intros a b.
  induction a as [| a' IH].
  - apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm.
    apply IH.
Qed.

Lemma S_a_plus_b:
  forall a b, S (a + b) = S a + b.
Proof.
  intros a b.
  reflexivity.
Qed.

Lemma S_a_le_S_a_plus_b:
  forall a b, S a <= S (a + b) /\ S b <= S (a + b).
Proof.
  intros. split.
  - rewrite S_a_plus_b. apply le_plus_l.
  - rewrite plus_comm. rewrite S_a_plus_b.
    apply le_plus_l.
Qed.

Theorem plus_lt:
  forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H.
  inversion H.
  - apply S_a_le_S_a_plus_b.
  - assert (H' := S_a_le_S_a_plus_b n1 n2).
    destruct H' as [H'1 H'2].
    split.
    + apply le_trans with (S (n1 + n2)).
      * apply H'1.
      * apply le_S. apply H0.
    + apply le_trans with (S (n1 + n2)).
      * apply H'2.
      * apply le_S. apply H0.
Qed.

Theorem lt_S: forall n m,
  n < m -> n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S. apply H.
Qed.

Theorem leb_complete:
  forall n m, n <=? m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n as [| n' IH].
  - intros. apply O_le_n.
  - intros. destruct m.
    + discriminate.
    + apply n_le_m__Sn_le_Sm.
      apply IH.
      apply H.
Qed.

Theorem leb_correct:
  forall n m, n <= m -> n <=? m = true.
Proof.
  intros n m.
  generalize dependent m.
  induction n as [| n' IH].
  - intros. reflexivity.
  - intros. destruct m.
    + inversion H.
    + apply IH.
      apply Sn_le_Sm__n_le_m.
      apply H.
Qed.

Theorem leb_true_trans: forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply leb_correct.
  apply le_trans with m.
  apply H1. apply H2.
Qed.

(* Exercise 11 *)
Theorem leb_iff:
  forall n m, n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split. apply leb_complete. apply leb_correct.
Qed.

(* Exercise 12 *)
(* this is kinda like a vector space(although technically not since natural number is not a field) *)
(* the "bases" of this "vs" is (1, 0, 1), (0, 1, 1), (-1, -1, -2) *)
(* 1.
  R 1 1 2 is provable(apply C3, C2, and C1)
  R 2 2 6 is not
*)

(* c5 and c4 are both not necessary; c4 is the inverse of c2 . c3 *)

Inductive R: nat -> nat -> nat -> Prop :=
  | c1: R 0 0 0
  | c2 m n o (H: R m n o): R (S m) n (S o)
  | c3 m n o (H: R m n o): R m (S n) (S o).
  (* | c4 m n o (H: R (S m) (S n) (S (S o))): R m n o *)
  (* | c5 m n o (H: R m n o): R n m o. *)

(* Exercise 13 *)
Definition fR: nat -> nat -> nat := fun n m => n + m.

Theorem R_equiv_fR:
  forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR.
  intros m n o. split.
  - intros H.
    induction H as [| m' n' o' H' | m' n' o' H'].
    + reflexivity.
    + simpl. rewrite IHH'. reflexivity.
    + rewrite plus_comm. simpl.
      rewrite plus_comm. rewrite IHH'. reflexivity.
  - intros H.
    generalize dependent n.
    generalize dependent o.
    induction m as [| m' IH].
    + intros. simpl in H. rewrite H.
      generalize dependent n.
      induction o as [| o' IH].
      * intros. apply c1.
      * intros.
        apply c3.
        apply IH with o'.
        reflexivity.
    + intros.
      destruct o.
      * discriminate.
      * apply c2.
        apply IH.
        simpl in H.
        injection H as H.
        apply H.
Qed.

(* Exercise 14 *)
Inductive subseq: list nat -> list nat -> Prop :=
  | subseq_nil l: subseq [] l
  | subseq_app_any n l1 l2 (H: subseq l1 l2): subseq l1 (n :: l2)
  | subseq_app_same n l1 l2 (H: subseq l1 l2): subseq (n :: l1) (n :: l2).

Theorem subseq_refl: forall l, subseq l l.
Proof.
  intros l.
  induction l as [| a t IH].
  - apply subseq_nil.
  - apply subseq_app_same. apply IH.
Qed.

Theorem subseq_nil_nil:
  forall l, subseq l [] -> l = [].
Proof.
  induction l as [| a t IH].
  - reflexivity.
  - intros.
    inversion H.
Qed.

Lemma eq_eq:
  forall n m, n =? m = true -> n = m.
Proof.
  induction n as [| n' IH].
  - intros. destruct m.
    + reflexivity.
    + discriminate.
  - intros. destruct m.
    + discriminate.
    + apply f_equal.
      apply IH.
      apply H.
Qed.

Theorem subseq_app:
  forall (l1 l2 l3: list nat),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H.
  - apply subseq_nil.
  - simpl. apply subseq_app_any.
    apply IHsubseq.
  - simpl. apply subseq_app_same.
    apply IHsubseq.
Qed.

Theorem subseq_trans:
  forall (l1 l2 l3: list nat),
    subseq l1 l2 ->
    subseq l2 l3 ->
    subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  generalize dependent l1.
  induction H2.
  - intros.
    apply subseq_nil_nil in H1.
    rewrite H1.
    apply subseq_nil.
  - intros.
    apply subseq_app_any.
    apply IHsubseq.
    apply H1.
  - intros.
    inversion H1.
    + apply subseq_nil.
    + apply subseq_app_any.
      apply IHsubseq.
      apply H3.
    + apply subseq_app_same.
      apply IHsubseq.
      apply H3.
Qed.

(* Exercise 15 *)
(* R 2 [1;0] is provable *)
(* R 1 [1;2;1;0] is provable *)
(* R 6 [3;2;1;0] is not provable *)
