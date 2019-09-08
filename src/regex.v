Set Warnings "-notation-overridden,-parsing".
Require Export indprop.
Require Export lists.
Require Export Coq.Strings.Ascii.

Definition string := list ascii.

Lemma provable_equiv_true:
  forall (P: Prop), P -> (P <-> True).
Proof.
  intros P HP.
  split.
  - intros _. apply I.
  - intros _. apply HP.
Qed.

Lemma not_equiv_false:
  forall (P: Prop), ~P -> (P <-> False).
Proof.
  intros P HNP.
  split.
  - intros HP. destruct (HNP HP).
  - intros F. destruct F.
Qed.

Lemma null_matches_none:
  forall (s: string), (s =~ EmptySet) <-> False.
Proof.
  intros s.
  apply not_equiv_false.
  unfold not. intros. inversion H.

  (* split.
  - intros Hs. inversion Hs.
  - intros F. destruct F. *)
Qed.

Lemma empty_matches_eps:
  forall (s: string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne:
  forall (a: ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma char_nomatch_char:
  forall (a b: ascii) s,
    b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

Lemma char_eps_suffix:
  forall (a: ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists:
  forall (s: string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros s re0 re1.
  split.
  - intros H.
    inversion H.
    exists s1, s2.
    split. reflexivity.
    split. apply H3. apply H4.
  - intros [s0 [s1 [H1 [H2 H3]]]].
    rewrite H1.
    apply MApp. apply H2. apply H3.
Qed.

(* Exercise 1 *)
Lemma app_ne:
  forall (a: ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros a s re0 re1.
  split.
  - intros H.
    apply app_exists in H.
    destruct H as [s0 [s1 H]].
    destruct s0 as [|a' s0'].
    + simpl in H.
      destruct H as [H0 [H1 H2]].
      left. split. apply H1. rewrite H0. apply H2.
    + simpl in H.
      destruct H as [H0 [H1 H2]].
      right. exists s0', s1.
      inversion H0.
      split. reflexivity.
      split. apply H1.
      apply H2.
  - intros [[H0 H1] | [s0 [s1 [H0 [H1 H2]]]]].
    + apply (MApp [] re0 (a :: s) re1 H0 H1).
    + rewrite H0.
      assert (H': a :: s0 ++ s1 = (a :: s0) ++ s1).
      { reflexivity. }
      rewrite H'.
      apply MApp. apply H1. apply H2.
Qed.

Lemma union_disj:
  forall (s: string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.






















