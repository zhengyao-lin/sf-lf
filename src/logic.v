Set Warnings "-notation-overridden,-parsing".
Require Export tactics.

Definition injective {A B} (f: A -> B) :=
  forall x y: A, f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise 1 *)
Example and_exercise:
  forall n m: nat,
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n.
    + reflexivity.
    + discriminate.
  - destruct n.
    + simpl in H. apply H.
    + discriminate.
Qed.

Lemma proj1: forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

(* Exercise 2 *)
Lemma proj2: forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ.
Qed.

Theorem and_commut: forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.
Qed.

(* Exercise 3 *)
Theorem and_assoc: forall P Q R: Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma or_example:
  forall n m: nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro:
  forall A B: Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ:
  forall n: nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem ex_falso_quodlibet:
  forall (P: Prop), False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not:
  forall (P: Prop),
  ~P -> (forall (Q: Prop), P -> Q).
Proof.
  intros P HP Q P'.
  destruct (HP P').
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one: 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate.
Qed.

Theorem not_False: ~False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything:
  forall P Q : Prop, (P /\ not P) -> Q.
Proof.
  intros P Q [HP HNP].
  unfold not in HNP.
  destruct (HNP HP).
Qed.

Theorem double_neg:
  forall P: Prop,
  P -> ~~P.
Proof.
  intros P proof_of_P.
  unfold not.
  intros proof_of_not_P.
  destruct (proof_of_not_P proof_of_P).
Qed.

(* Exercise 4 *)
Theorem contrapositive:
  forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros HNQ HP.
  destruct (HNQ (H HP)).
Qed.

(* Exercise 5 *)
Theorem not_both_true_and_false:
  forall P: Prop,
  ~(P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [HP HNP].
  destruct (HNP HP).
Qed.

Theorem not_true_is_false:
  forall b: bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    assert (H': true = true). { reflexivity. }
    destruct (H H').
    (* unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. *)
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false':
  forall b: bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma True_is_true: True.
Proof. apply I. Qed.

Theorem iff_sym:
  forall P Q: Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Lemma not_true_iff_false:
  forall b, b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.

  (*
  intros b.
  destruct b.
  - split.
    + intro H.
      apply not_true_is_false.
      apply H.
    + intro H.
      discriminate.
  - split.
    + intro H.
      reflexivity.
    + unfold not.
      intros _ H.
      discriminate.
  *)
Qed.

(* Exercise 6 *)
Theorem or_distributes_over_and:
  forall P Q R: Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | [HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. split. apply HQ. apply HR.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m. destruct n as [|n']. 
    + intros _. left. reflexivity.
    + destruct m as [|m'].
        - intros _. right. reflexivity.
        - intros contra. inversion contra.
Qed.

Lemma mult_0:
  forall n m,
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc:
  forall P Q R: Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3:
  forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example:
  forall n m: nat,
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even:
  exists n: nat, 4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2:
  forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(* Exercise 7 *)
Theorem dist_not_exists:
  forall (X: Type) (P: X -> Prop),
  (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros X P.
  intros H.
  intros [x H'].
  destruct (H' (H x)).
Qed.

Theorem dist_not_forall:
  forall (X: Type) (P: X -> Prop),
  (exists x, P x) -> ~(forall x, ~P x).
Proof.
  intros X P.
  intros [x H].
  intros H'.
  destruct (H' x H).
Qed.

(* Exercise 8 *)
Theorem dist_exists_or:
  forall (X: Type) (P Q: X -> Prop),
  (exists x, P x \/ Q x) <->
  (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x1 HP] | [x2 HQ]].
    + exists x1. left. apply HP.
    + exists x2. right. apply HQ.
Qed.

Fixpoint In {A: Type} (x: A) (l: list A): Prop :=
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
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map:
  forall (A B: Type) (f: A -> B) (l: list A) (x: A),
  In x l ->
  In (f x) (map f l).
Proof.
  intros A B f.
  induction l as [| a t IH].
  - intros x H.
    destruct H.
  - simpl.
    intros x [H1 | H2].
    + left. apply f_equal. apply H1.
    + right. apply IH. apply H2.
Qed.

(* Exercise 9 *)
Lemma In_map_iff:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (map f l) <->
  exists x, f x = y /\ In x l.
Proof.
  intros A B f.
  induction l as [| a t IH].
  - split.
    + intros H.
      destruct H.
    + intros [x [_ H]].
      destruct H.
  - split.
    + intros [H1 | H2].
      * exists a. split.
        -- apply H1.
        -- left. reflexivity.
      * apply IH in H2.
        destruct H2 as [x [H2 H3]].
        exists x. split.
        -- apply H2.
        -- right. apply H3.
    + intros [x [H1 H2]].
      simpl. simpl in H2.
      destruct H2 as [H3 | H4].
      * left. rewrite H3. apply H1.
      * right. apply IH. exists x. split.
        apply H1. apply H4.
Qed.

(* Exercise 10 *)
Lemma In_app_iff:
  forall A l l' (a: A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A.
  induction l as [| a t IH].
  - intros l' a. split.
    + intros H. right. apply H.
    + intros [H1 | H2].
      * destruct H1.
      * apply H2.
  - intros l' x. split.
    + intros [H1 | H2]. 
      * left. left. apply H1.
      * apply IH in H2.
        destruct H2 as [H3 | H4].
        -- left. right. apply H3.
        -- right. apply H4.
    + intros [[H1 | H2] | H3].
      * left. apply H1.
      * right. apply IH. left. apply H2.
      * right. apply IH. right. apply H3.
Qed.

(* Exercise 11 *)
Fixpoint All {T: Type} (P: T -> Prop) (l: list T): Prop :=
  match l with
  | [] => True
  | a :: t => P a /\ All P t
  end.

Lemma All_In:
  forall T (P: T -> Prop) (l: list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T.
  induction l as [| a t IH].
  - split.
    + intros H. apply I.
    + intros H0 x H.
      destruct H.
  - split.
    + intros H. split.
      * apply H. left. reflexivity.
      * apply IH. intros x H2.
        apply H. right. apply H2.
    + intros [H1 H2] x H3.
      destruct H3 as [H4 | H5].
      * rewrite <- H4. apply H1.
      * apply IH. apply H2. apply H5.
Qed.

(* Exercise 12 *)
Definition combine_odd_even
  (Podd Peven: nat -> Prop): nat -> Prop :=
  fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop) (n: nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n.
  intros H1 H2.
  destruct (oddb n) eqn:E.
  - unfold combine_odd_even.
    rewrite E. apply H1.
    reflexivity.
  - unfold combine_odd_even.
    rewrite E. apply H2.
    reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven: nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n.
  intros H H1.
  unfold combine_odd_even in H.
  rewrite H1 in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven: nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n.
  intros H H1.
  unfold combine_odd_even in H.
  rewrite H1 in H.
  apply H.
Qed.

Lemma plus_comm3:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  (* WORKED IN CLASS *)
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil:
  forall A (x: A) (l: list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Axiom functional_extensionality:
  forall {X Y: Type} {f g : X -> Y},
  (forall (x: X), f x = g x) -> f = g.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(* Print Assumptions function_equality_ex2. *)

(* Exercise 13 *)
Fixpoint rev_append {X} (l1 l2: list X): list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l: list X): list X :=
  rev_append l [].

Lemma rev_append_assoc:
  forall X (l1 l2 l3: list X),
    rev_append l1 l2 ++ l3 =
    rev_append l1 (l2 ++ l3).
Proof.
  intros X l1.
  induction l1 as [| a' t' IH'].
  - reflexivity.
  - intros l2 l3. simpl.
    apply IH'.
Qed.

Lemma tr_rev_correct: forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  induction x as [| a t IH].
  - reflexivity.
  - simpl. rewrite <- IH.
    unfold tr_rev.
    rewrite rev_append_assoc.
    reflexivity.
Qed.

Theorem evenb_double:
  forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* Exercise 14 *)
Theorem evenb_double_conv:
  forall n, exists k,
  n = if evenb n then double k
      else S (double k).
Proof.
  induction n as [| n' [k IH']].
  - exists 0. reflexivity.
  - destruct (evenb (S n')) eqn:E.
    + exists (S k).
      rewrite IH'.
      rewrite evenb_S in E.
      destruct (evenb n').
      * discriminate.
      * reflexivity.
    + exists k.
      rewrite IH'.
      rewrite evenb_S in E.
      destruct (evenb n').
      * reflexivity.
      * discriminate.
Qed.

Theorem even_bool_prop:
  forall n, evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H.
    destruct (evenb_double_conv n) as [k H'].
    exists k.
    rewrite H in H'.
    apply H'.
  - intros [k H].
    rewrite H.
    apply evenb_double.
Qed.

Theorem eqb_refl: forall n: nat,
  true = (n =? n).
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem eqb_eq:
  forall n1 n2: nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

(* Exercise 15 *)
Lemma andb_true_iff:
  forall b1 b2: bool,
  andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H.
    destruct b1.
    + destruct b2.
      * split. reflexivity. reflexivity.
      * discriminate.
    + discriminate.
  - intros [H1 H2].
    rewrite H1, H2.
    reflexivity.
Qed.

Lemma orb_true_iff:
  forall b1 b2,
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H.
    destruct b1.
    + destruct b2.
      * right. reflexivity.
      * left. reflexivity.
    + destruct b2.
      * right. reflexivity.
      * discriminate.
  - intros [H1 | H2].
    + rewrite H1. reflexivity.
    + rewrite H2. destruct b1.
      * reflexivity.
      * reflexivity.
Qed.

(* Exercise 16 *)
Theorem eqb_neq:
  forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
(*
  induction x as [| n' IH].
  - intros y. split.
    + intros H H'.
      rewrite <- H' in H.
      discriminate.
    + intros H.
      destruct y.
      * exfalso.
        apply H.
        reflexivity.
      * reflexivity.
  - intros y. split.
    + destruct y.
      * intros H H'.
        discriminate.
      * intros H.
        simpl in H.
        apply IH in H.
        intros H'.
        injection H' as H1.
        destruct (H H1).
    + destruct y.
      * intros _. reflexivity.
      * intros H. apply IH.
        intros H'.
        apply (f_equal nat nat S n' y) in H'.
        destruct (H H').
*)
  intros x y.
  rewrite <- not_true_iff_false.
  rewrite <- eqb_eq.
  reflexivity.
Qed.

(* Exercise 17 *)
Fixpoint eqb_list {A: Type} (eqb: A -> A -> bool)
                  (l1 l2: list A): bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | a1 :: t1, a2 :: t2 => andb (eqb a1 a2) (eqb_list eqb t1 t2)
  end.

Lemma eqb_list_true_iff:
  forall A (eqb: A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H.
  induction l1 as [| a t IH].
  - destruct l2.
    + split.
      intros _. reflexivity.
      intros _. reflexivity.
    + split.
      * intros H'. discriminate.
      * intros H'. discriminate.
  - destruct l2.
    + split.
      * intros H'. discriminate.
      * intros H'. discriminate.
    + simpl. split.
      * intros H'. apply andb_true_iff in H'.
        destruct H' as [H1 H2].
        apply H in H1.
        apply IH in H2.
        rewrite H1, H2.
        reflexivity.
      * intros H'.
        injection H' as H1 H2.
        apply H in H1.
        apply IH in H2.
        rewrite H1, H2.
        reflexivity.
Qed.

(* Exercise 18 *)
Theorem forallb_true_iff:
  forall X test (l: list X),
  forallb test l = true <->
  All (fun x => test x = true) l.
Proof.
  intros X test.
  induction l as [| a t IH].
  - split.
    + intros _. reflexivity.
    + intros _. reflexivity.
  - split.
    + intros H. apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply IH in H2.
      split. apply H1. apply H2.
    + intros [H1 H2].
      apply IH in H2.
      simpl. rewrite H1. rewrite H2.
      reflexivity.
Qed.

(* not derivable *)
Definition excluded_middle := forall P: Prop, P \/ ~P.

Theorem restricted_excluded_middle:
  forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H.
    intros contra. discriminate contra.
Qed.

(* Exercise 19 *)
Theorem excluded_middle_irrefutable:
  forall (P: Prop), ~~(P \/ ~P).
Proof.
  intros P H.
  unfold not in H.
  apply H.
  right.
  intros HP.
  apply H.
  left.
  apply HP.
Qed.

(* Exercise 20 *)
Theorem not_exists_dist:
  excluded_middle ->
  forall (X: Type) (P: X -> Prop),
    ~(exists x, ~P x) -> (forall x, P x).
Proof.
  intros EM X P.
  unfold not.
  intros H.
  intros x.

  destruct (EM (P x)) as [EM1 | EM2].
  - apply EM1.
  - exfalso. apply H.
    exists x.
    apply EM2.
Qed.

(* Exercise 21 *)
(* Definition excluded_middle := forall P: Prop, P \/ ~P. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P: Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q: Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q: Prop,
  (P -> Q) -> (~P \/ Q).

Fact dne_eq_lem: double_negation_elimination <-> excluded_middle.
Proof.
  split.
  - intros dne.
    intros P.
    apply dne.
    apply excluded_middle_irrefutable.
  - intros lem.
    intros P H.
    destruct (lem P) as [lem1 | lem2].
    + apply lem1.
    + destruct (H lem2).
Qed.

Fact dmnn_eq_lem: de_morgan_not_and_not <-> excluded_middle.
Proof.
  split.
  - intros dmnn.
    intros P.
    apply dmnn.
    intros [H1 H2].
    destruct (H2 H1).
  - intros lem.
    intros P Q H.
    destruct (lem P) as [H1 | H2].
    + left. apply H1.
    + destruct (lem Q) as [H3 | H4].
      * right. apply H3.
      * exfalso. apply H.
        split. apply H2. apply H4.
Qed.

