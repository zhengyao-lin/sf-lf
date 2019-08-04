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

Inductive reg_exp {T: Type}: Type :=
  | EmptySet
  | EmptyStr
  | Char (t: T)
  | App (r1 r2: reg_exp)
  | Union (r1 r2: reg_exp)
  | Star (r: reg_exp).

Inductive exp_match {T}: list T -> reg_exp -> Prop :=
  | MEmpty: exp_match [] EmptyStr
  | MChar x: exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
      (H1: exp_match s1 re1)
      (H2: exp_match s2 re2):
      exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
      (H1 : exp_match s1 re1):
      exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
      (H2: exp_match s2 re2):
      exp_match s2 (Union re1 re2)
  | MStar0 re: exp_match [] (Star re)
  | MStarApp s1 s2 re
      (H1: exp_match s1 re)
      (H2: exp_match s2 (Star re)):
      exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l: list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1:
  forall T s (re: @reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s []).
  - apply H.
  - apply MStar0.
Qed.

(* Exercie 16 *)
Lemma empty_is_empty:
  forall T (s: list T),
  ~(s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion':
  forall T (s: list T) (re1 re2: @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [match1 | match2].
  - apply MUnionL. apply match1.
  - apply MUnionR. apply match2.
Qed.

Lemma MStar':
  forall T (ss: list (list T)) (re: reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss as [| a t IH].
  - simpl. apply MStar0.
  - simpl.
    apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IH. intros s H'.
      apply H. simpl. right. apply H'.
Qed.

(* Exercise 17 *)
Lemma reg_exp_of_list_spec:
  forall T (s1 s2: list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  (* a much nicer version from https://github.com/cz717/bksol/blob/master/sf/IndProp.v
  intros T s1 s2.
  generalize dependent s1.
  induction s2 as [|h t].
  - (* s2 = [] *)
    split. 
    + intros H. simpl in H. inversion H. reflexivity.
    + intros H. simpl. rewrite H. apply MEmpty.
  - (* s2 = h::t *)
    intros s1. split. 
    + intros H. simpl in H. inversion H. 
      inversion H3. simpl. 
      rewrite (IHt s2) in H4. rewrite H4. reflexivity.
    + intros H. simpl. rewrite H.
      assert ( A : forall S (x:S) y, [x]++y = x::y).
      {  intros S x y. simpl. reflexivity.  }
      rewrite <- A. apply MApp.
      * apply MChar.
      * apply IHt. reflexivity.
  *)

  intros T s1 s2. split.
  - generalize dependent s2.
    generalize dependent s1.
    induction s1 as [| a1 t1 IH1].
    + destruct s2.
      * intros. reflexivity.
      * intros. simpl in H.
        inversion H.
        inversion H3.
        rewrite <- H5 in H1.
        discriminate H1.
    + intros s2 H.
      destruct s2.
      * simpl in H.
        inversion H.
      * simpl in H.
        inversion H.
        inversion H3.
        simpl.
        rewrite <- H5 in H1.
        injection H1 as H1.
        rewrite H6 in H4.
        rewrite H6.
        apply IH1 in H4.
        rewrite H4.
        reflexivity.
  - generalize dependent s2.
    generalize dependent s1.
    induction s1 as [| a1 t1 IH1].
    + intros. rewrite <- H. simpl. apply MEmpty.
    + intros.
      destruct s2.
      * discriminate.
      * simpl.
        assert (H': a1 :: t1 = [a1] ++ t1).
        { reflexivity. }
        rewrite H'.
        apply MApp.
        -- injection H as H1 H2.
           rewrite H1.
           apply MChar.
        -- injection H as _ H2.
           apply IH1. apply H2.
Qed.

Fixpoint re_chars {T} (re: reg_exp): list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match:
  forall T (s: list T) (re: reg_exp) (x: T),
    s =~ re ->
    In x s ->
    In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - simpl.
    rewrite In_app_iff in Hin.
    destruct Hin as [H1 | H2].
    + apply IH1. apply H1.
    + apply IH2. apply H2.
Qed.

(* Exercise 18 *)
Fixpoint re_not_empty {T: Type} (re: @reg_exp T): bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char t => true
  | App r1 r2 => re_not_empty r1 && re_not_empty r2
  | Union r1 r2 => re_not_empty r1 || re_not_empty r2
  | Star r => true
  end.

Lemma orb_comm:
  forall a b, orb a b = orb b a.
Proof.
  destruct a.
  - destruct b.
    + reflexivity.
    + reflexivity.
  - destruct b.
    + reflexivity.
    + reflexivity.
Qed.

Lemma re_not_empty_correct:
  forall T (re: @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros [s H].
    induction H as
      [
      | x'
      | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
      | s1 re1 re2 Hmatch IH
      | re1 s2 re2 Hmatch IH
      | re
      | s1 s2 re Hmatch1 IH1 Hmatch2 IH2
      ].
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IH1, IH2. reflexivity.
    + simpl. rewrite IH. reflexivity.
    + simpl. rewrite IH. rewrite orb_comm. reflexivity.
    + reflexivity.
    + apply IH2.
  - intros H.
    induction re as
      [
      |
      | t
      | r1 IH1 r2 IH2
      | r1 IH1 r2 IH2
      | r IH
      ].
    + discriminate.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2].
      destruct (IH1 H1) as [s1 H1'].
      destruct (IH2 H2) as [s2 H2'].
      exists (s1 ++ s2).
      apply MApp. apply H1'. apply H2'.
    + simpl in H. apply orb_true_iff in H.
      destruct H as [H1 | H2].
      * destruct (IH1 H1) as [s H1'].
        exists s. apply MUnionL. apply H1'.
      * destruct (IH2 H2) as [s H2'].
        exists s. apply MUnionR. apply H2'.
    + exists []. apply MStar0.
Qed.

Lemma star_app':
  forall T (s1 s2: list T) (re re': @reg_exp T),
    re' = Star re ->
    s1 =~ re' ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1' s2' re re' H0 H1 H2.
  induction H1 as
    [
    | x'
    | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH
    | re1 s2 re2 Hmatch IH
    | re''
    | s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2
    ].
  - apply H2.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - apply H2.
  - rewrite <- H0 in *.
    rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2. reflexivity.
Qed.

Lemma star_app:
  forall T (s1 s2: list T) (re: @reg_exp T),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  induction H1 as
    [
    | x'
    | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH
    | re1 s2' re2 Hmatch IH
    | re''
    | s1' s2' re'' Hmatch1 IH1 Hmatch2 IH2
    ].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - intros H. apply H.
  - intros H.
    rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2. apply Heqre'. apply H.
Qed.

(* Exercise 19 *)
Lemma MStar'':
  forall T (s: list T) (re: reg_exp),
    s =~ Star re ->
    exists (ss: list (list T)),
      s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H1.
  remember (Star re) as re'.
  induction H1 as
    [
    |
    |
    |
    |
    | re2
    | s1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    ].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split.
    reflexivity.
    intros s' H.
    destruct H.
  - destruct (IH2 Heqre') as [ss [H1 H2]].
    exists (s1 :: ss). split.
    + simpl. rewrite H1. reflexivity.
    + intros s' [H3 | H3].
      * rewrite <- H3.
        injection Heqre' as Heqre'.
        rewrite <- Heqre'. apply Hmatch1.
      * apply H2. apply H3.
Qed.

(* Exercise 20 *)
Fixpoint pumping_constant {T} (re: @reg_exp T): nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n: nat) (l: list T): list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus:
  forall T (n m: nat) (l: list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma le_false_le:
  forall a b,
    a <=? b = false ->
    b <= a.
Proof.
  induction a as [| a' IH].
  - intros. discriminate.
  - intros.
    destruct (a' =? b) eqn:E1.
    + apply eqb_eq in E1.
      rewrite E1.
      apply le_S. apply le_n.
    + apply le_S. apply IH.
      destruct (a' <=? b) eqn:E2.
      * apply leb_complete in E2.
        inversion E2.
        -- rewrite H1 in E1.
           rewrite <- eqb_refl in E1.
           discriminate.
        -- apply n_le_m__Sn_le_Sm in H0.
           rewrite H2 in H0.
           apply leb_correct in H0.
           rewrite H0 in H.
           discriminate.
      * reflexivity.
Qed.

Lemma le_plus_b:
  forall a b c,
    a <= b <-> a + c <= b + c.
Proof.
  intros a b c.
  induction c as [| c' IH].
  - split.
    + intros. rewrite (plus_comm a 0), (plus_comm b 0).
      simpl. apply H.
    + intros. rewrite (plus_comm a 0), (plus_comm b 0) in H.
      simpl in H. apply H.
  - split.
    + intros.
      rewrite (plus_comm a (S c')), (plus_comm b (S c')).
      rewrite <- S_a_plus_b.
      rewrite <- S_a_plus_b.
      apply n_le_m__Sn_le_Sm.
      rewrite (plus_comm c' a), (plus_comm c' b).
      apply IH.
      apply H.
    + intros.
      rewrite (plus_comm a (S c')), (plus_comm b (S c')) in H.
      rewrite <- S_a_plus_b in H.
      rewrite <- S_a_plus_b in H.
      apply Sn_le_Sm__n_le_m in H.
      rewrite (plus_comm c' a), (plus_comm c' b) in H.
      apply IH in H. apply H.
Qed.

Lemma le_lem:
  forall a b c d,
    a + b <= c + d ->
    a <= c \/ b <= d.
Proof.
  intros a b c d H.
  destruct (a <=? c) eqn:E1.
  - apply leb_complete in E1.
    left. apply E1.
  - apply le_false_le in E1.
    apply (le_plus_b c a d) in E1.
    assert (H' := le_trans _ _ _ H E1).
    rewrite (plus_comm a b), (plus_comm a d) in H'.
    apply le_plus_b in H'.
    right. apply H'.
Qed.

Theorem le_plus_r:
  forall a b c, a + b <= c -> a <= c.
Proof.
  intros a b c H.
  induction b as [| b' IH].
  - rewrite plus_comm in H. simpl in H.
    apply H.
  - apply IH. rewrite plus_comm in H.
    rewrite <- S_a_plus_b in H.
    destruct c.
    + inversion H.
    + apply Sn_le_Sm__n_le_m in H.
      apply le_S.
      rewrite plus_comm in H.
      apply H.
Qed.

Lemma list_length_0:
  forall X l, @length X l = 0 -> l = [].
Proof.
  intros.
  destruct l.
  - reflexivity.
  - discriminate.
Qed.

Lemma pumping:
  forall T (re: @reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
      s2 <> [] /\
      forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch as
    [
    | x
    | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
    | s1 re1 re2 Hmatch IH
    | re1 s2 re2 Hmatch IH
    | re
    | s1 s2 re Hmatch1 IH1 Hmatch2 IH2
    ].
  - simpl. intros. inversion H.
  - simpl. intros. inversion H. inversion H2.
  - simpl. intros.
    rewrite app_length in H.
    apply le_lem in H. destruct H as [H | H].
    + (* s1 is longer than the pumping length of re1 *)
      destruct (IH1 H) as
        [s1'x
          [s1'y
            [s1'z
              [IH1'1 [IH1'2 IH1'3]]
            ]
          ]
        ].
      exists s1'x, s1'y, (s1'z ++ s2).
      split.
      { rewrite IH1'1.
        rewrite app_assoc, app_assoc, app_assoc.
        reflexivity. }
      split.
      { apply IH1'2. }
      { intros.
        rewrite app_assoc, app_assoc.
        apply MApp.
        - rewrite <- app_assoc. apply IH1'3.
        - apply Hmatch2. }
    + (* s2 is longer than the pumping length of re2 *)
      destruct (IH2 H) as
        [s2'x
          [s2'y
            [s2'z
              [IH2'1 [IH2'2 IH2'3]]
            ]
          ]
        ].
      exists (s1 ++ s2'x), s2'y, s2'z.
      split.
      { rewrite IH2'1.
        rewrite app_assoc, app_assoc.
        reflexivity. }
      split.
      { apply IH2'2. }
      { intros.
        rewrite <- app_assoc.
        apply MApp.
        - apply Hmatch1.
        - apply IH2'3. }
  - (* left union, pump in the same way as s1 *)
    intros. simpl in H.
    apply le_plus_r in H.
    destruct (IH H) as
      [s1'x
        [s1'y
          [s1'z
            [IH1 [IH2 IH3]]
          ]
        ]
      ].
    exists s1'x, s1'y, s1'z.
    split.
    { apply IH1. }
    split.
    { apply IH2. }
    { intros. apply MUnionL. apply IH3. }
  - (* right union, pump in the same way as s2 *)
    intros. simpl in H.
    rewrite plus_comm in H.
    apply le_plus_r in H.
    destruct (IH H) as
      [s2'x
        [s2'y
          [s2'z
            [IH1 [IH2 IH3]]
          ]
        ]
      ].
    exists s2'x, s2'y, s2'z.
    split.
    { apply IH1. }
    split.
    { apply IH2. }
    { intros. apply MUnionR. apply IH3. }
  - intros. inversion H.
  - intros. simpl in H. rewrite app_length in H.
    destruct (length s1) eqn:E.
    + (* if s1 is empty, pump the same way as s2 *)
      simpl in H.
      apply list_length_0 in E.
      rewrite E. simpl.
      apply (IH2 H).
    + (* s1 non empty, pump with s1 *)
      exists [], s1, s2.
      split.
      { reflexivity. }
      split.
      { destruct s1. discriminate.
        intros H'. discriminate. }
      { simpl. intros m.
        induction m as [| m' IH].
        - simpl. apply Hmatch2.
        - assert (H': S m' = 1 + m').
          { reflexivity. }
          rewrite H'.
          rewrite napp_plus.
          rewrite <- app_assoc.
          apply MStarApp.
          + simpl. rewrite app_nil_r. apply Hmatch1.
          + apply IH. }
Qed.
