Set Warnings "-notation-overridden,-parsing".
Require Export indprop.

Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Theorem ev_8: even 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8': even 8 :=
  (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).

Module Props.

Module And.

Inductive and (P Q: Prop): Prop :=
  | conj: P -> Q -> and P Q.

Theorem wth: forall (P Q: Prop), and P Q -> P /\ Q.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  apply HP. apply HQ.
Qed.

End And.

Print prod.
Print and.

Lemma and_comm: forall P Q: Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition conj_fact:
  forall P Q R,
    P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R HPQ HQR =>
    match HPQ, HQR with
    | conj HP HQ, conj _ HR =>
      conj HP HR
    end.

Definition or_comm:
  forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ =>
    match HPQ with
    | or_introl HP => or_intror HP
    | or_intror HQ => or_introl HQ
    end.

Module Ex.
  Inductive ex {A: Type} (P: A -> Prop): Prop :=
    | ex_intro: forall x: A, P x -> ex P.
End Ex.

Check ex (fun n => even n).

Definition some_nat_is_even: exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

Check ex_intro even 4.

Definition ex_ev_Sn: ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (ev_SS 0 ev_0).

Inductive True: Prop :=
  | I: True.

Inductive False: Prop := .

End Props.

Module MyEquality.

Inductive eq {X: Type}: X -> X -> Prop :=
  | eq_refl: forall x, eq x x.

Notation "x == y" := (eq x y)
                     (at level 70, no associativity)
                     : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  simpl.
  apply eq_refl.
Qed.

Definition four': 2 + 2 == 1 + 3 := eq_refl 4.

Definition singleton:
  forall (X: Type) (x: X),
    []++[x] == x::[] :=
    fun (X: Type) (x: X) => eq_refl [x].

Lemma equality__leibniz_equality:
  forall (X: Type) (x y: X),
    x == y -> forall P: X -> Prop, P x -> P y.
Proof.
  intros X x y Hxy P HPx.
  destruct Hxy as [x].
  apply HPx.
Qed.

Lemma leibniz_equality__equality:
  forall (X: Type) (x y: X),
    (forall P: X -> Prop, P x -> P y) -> x == y.
Proof.
  intros X x y leibniz.
  apply (leibniz (eq x) (eq_refl x)).
Qed.

End MyEquality.
