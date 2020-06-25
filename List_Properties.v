
Require Import String.
Import List.
Import ListNotations.

Ltac nth_error_empty :=
  match goal with
  | [H : nth_error [] ?i = Some _ |- _] =>
      destruct i;
      simpl in H;
      discriminate
  end.


Lemma concat_cons: forall (A : Type) (l l' : list A) (e : A),
  l ++ (e :: l') = (l ++ [e]) ++ l'.
Proof.
  intros A l.
  induction l;
  intros l' e.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma cons_concat: forall (A : Type) (l : list A) (a1 a2 : A),
  a1 :: a2 :: l = [a1 ; a2] ++ l.
Proof.
  intros.
  trivial.
Qed.

Lemma concat_list_two: forall (A : Type) (l : list A) (a1 a2 : A),
  l ++ [a1 ; a2] = (l ++ [a1]) ++ [a2].
Proof.
  intros A l.
  induction l;
  intros a1 a2.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.


Lemma nth_different_tail_smaller:
  forall (A : Type) (l : list A) (i : nat) (a1 a2 : A),
  a1 <> a2 ->
  nth_error (l ++ [a1]) i = Some a2 ->
  nth_error l i = Some a2.
Proof.
  intros A l.
  induction l;
  intros i a1 a2;
  intros H_diff H_nth.
  - simpl in * |- *.
    destruct i;
    simpl in H_nth.
    + inversion H_nth.
      contradiction.
    + destruct i;
      simpl in H_nth;
      discriminate.
  - simpl in * |- *.
    destruct i;
    simpl in H_nth |- *.
    + assumption.
    + apply IHl with a1;
      assumption.
Qed.

Lemma nth_succes_larger:
  forall (A : Type) (l l' : list A) (i : nat) (a1 : A),
  nth_error l i = Some a1 ->
  nth_error (l ++ l') i = Some a1.
Proof.
  intros A l l' i a1.
  intros H_nth.
  rewrite nth_error_app1.
  - assumption.
  - apply nth_error_Some.
    unfold not.
    intros H_none.
    rewrite H_none in H_nth.
    discriminate.
Qed.

Lemma nth_index_in_concat:
  forall (A : Type) (l l' : list A) (i : nat) (a : A),
  nth_error (l ++ l') i = Some a ->
  nth_error l i = Some a \/ (exists j, j + (Datatypes.length l) = i /\ nth_error l' j = Some a).
Proof.
  intros.
  assert (i < Datatypes.length l \/ Datatypes.length l <= i) by apply PeanoNat.Nat.lt_ge_cases.
  destruct H0.
  - left.
    rewrite <- H.
    rewrite nth_error_app1.
    + reflexivity.
    + assumption.
  - right.
    exists (i - Datatypes.length l).
    split.
    + apply PeanoNat.Nat.sub_add.
      assumption.
    + rewrite <- H.
      rewrite nth_error_app2.
      * reflexivity.
      * assumption.
Qed.

Lemma nth_error_concat_not_in_tail_implies_head:
  forall (A : Type) (l l' : list A) (i : nat) (e : A),
  nth_error (l ++ l') i = Some e ->
  ~ In e l' ->
  nth_error l i = Some e.
Proof.
  intros A l.
  induction l;
  intros l' i e;
  intros H_nth H_not_in;
  simpl in H_nth.
  - apply nth_error_In in H_nth.
    contradiction.
  - destruct i;
    simpl in * |- *.
    + assumption.
    + eapply IHl;
      eassumption.
Qed.
