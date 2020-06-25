
Require Import String.
Import List.
Import ListNotations.

Set Implicit Arguments.
Require Import Flood_Box.


Lemma add_message_to_all_reveals_older_messages:
  forall buf buf' i' port_buf' i m c,
  buf' = add_message_to_all buf i m c ->
  nth_error buf' i' = Some port_buf' ->
  exists port_buf, port_buf' = (i, m, c) :: port_buf.
Proof.
  intros buf.
  induction buf;
  intros buf' i' port_buf' i m c;
  intros H_add H_nth.
  - simpl in H_add.
    subst.
    destruct i';
    simpl in H_nth;
    discriminate.
  - simpl in H_add.
    subst.
    destruct i';
    simpl in H_nth.
    + inversion H_nth.
      exists a.
      reflexivity.
    + apply IHbuf with (add_message_to_all buf i m c) i'.
      * reflexivity.
      * assumption.
Qed.

Lemma add_message_to_all_old_lookups:
  forall buf buf' port_buf' k i m c,
  buf' = add_message_to_all buf i m c ->
  nth_error buf' k = Some ((i, m, c) :: port_buf') ->
  nth_error buf k = Some port_buf'.
Proof.
  intros buf.
  induction buf;
  intros buf' port_buf' k i m c;
  intros H_add H_nth;
  simpl in H_add;
  subst.
  - destruct k;
    simpl in H_nth;
    discriminate.
  - destruct k;
    simpl in H_nth |- *.
    + inversion H_nth.
      reflexivity.
    + apply IHbuf with (add_message_to_all buf i m c) i m c.
      * reflexivity.
      * assumption.
Qed.

Lemma add_message_to_all_preserves_length:
  forall buf i m c,
  Datatypes.length buf = Datatypes.length (add_message_to_all buf i m c).
Proof.
  intros buf.
  induction buf;
  intros i m c;
  simpl.
  - reflexivity.
  - rewrite <- IHbuf.
    reflexivity.
Qed.
