
Require Import String.
Import List.
Import ListNotations.

Require Import Flood_Box.


Lemma extract_message_none_action_same_buffer:
  forall port_buf port_buf' i j m c,
  extract_message port_buf i j m c = (port_buf', None) ->
  port_buf = port_buf'.
Proof.
  intros port_buf.
  induction port_buf;
  intros port_buf' i j m c;
  intros H_extract.
  - simpl in H_extract.
    inversion H_extract.
    reflexivity.
  - simpl in H_extract.
    destruct a.
    destruct p.
    destruct (triple_and (Nat.eqb i n0) (m =? s)%string (Nat.eqb c n)).
    + inversion H_extract.
    + destruct (extract_message port_buf i j m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      assert (port_buf = i0) by (eapply IHport_buf; eassumption).
      subst.
      reflexivity.
Qed.

Lemma extract_port_buffer_none_action_same_buffer:
  forall buf buf' p i j m c,
  extract_port_buffer buf p i j m c = (buf', None) ->
  buf = buf'.
Proof.
  intros buf.
  induction buf;
  intros buf' p i j m c;
  intros H_extract.
  - simpl in H_extract.
    inversion H_extract.
    reflexivity.
  - simpl in H_extract.
    destruct p.
    + destruct (extract_message a i j m c) eqn:mes.
      inversion H_extract. subst.
      assert (a = i0)
        by (eapply extract_message_none_action_same_buffer; eassumption).
      subst.
      reflexivity.
    + destruct (extract_port_buffer buf p i j m c) eqn:extract.
      inversion H_extract. subst.
      assert (buf = i0) by (eapply IHbuf; eassumption).
      subst.
      reflexivity.
Qed.

Lemma extract_message_success_same_output:
  forall port_buf port_buf' i j m c i' j' m' c',
  extract_message port_buf i j m c = (port_buf', Some (j', i', m', c')) ->
  i = i' /\ j = j' /\ m = m' /\ c = c'.
Proof.
  intros port_buf.
  induction port_buf;
  intros port_buf' i j m c i' j' m' c';
  intros H_extract.
  - simpl in H_extract.
    inversion H_extract.
  - simpl in H_extract.
    destruct a.
    destruct p.
    destruct (triple_and (Nat.eqb i n0) (m =? s)%string (Nat.eqb c n)).
    + inversion H_extract.
      repeat split;
      reflexivity.
    + destruct (extract_message port_buf i j m c) eqn:extract.
      inversion H_extract.
      subst.
      eapply IHport_buf.
      eassumption.
Qed.

Lemma extract_port_buffer_success_same_output:
  forall buf buf' k i j m c i' j' m' c',
  extract_port_buffer buf k i j m c = (buf', Some (j', i', m', c')) ->
  i = i' /\ j = j' /\ m = m' /\ c = c'.
Proof.
  intros buf.
  induction buf;
  intros buf' k i j m c i' j' m' c';
  intros H_extract.
  - simpl in H_extract.
    inversion H_extract.
  - simpl in H_extract.
    destruct k.
    + destruct (extract_message a i j m c) eqn:mes.
      inversion H_extract.
      subst.
      eapply extract_message_success_same_output.
      eassumption.
    + destruct (extract_port_buffer buf k i j m c) eqn:extract.
      inversion H_extract.
      subst.
      eapply IHbuf.
      eassumption.
Qed.

Lemma extract_message_success_lookups_reveal_old:
  forall port_buf port_buf' i j m c h p m' c',
  extract_message port_buf i j m c = (port_buf', Some (j, i, m, c)) ->
  nth_error port_buf' h = Some (p, m', c') ->
  exists h', nth_error port_buf h' = Some (p, m', c').
Proof.
  intros port_buf.
  induction port_buf;
  intros port_buf' i j m c h p m' c';
  intros H_extract H_nth.
  - inversion H_extract.
  - simpl in H_extract.
    destruct a.
    destruct p0.
    destruct (triple_and (Nat.eqb i n0) (m =? s)%string (Nat.eqb c n)).
    + inversion H_extract.
      exists (S h).
      simpl.
      assumption.
    + destruct (extract_message port_buf i j m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      destruct h;
      simpl in H_nth.
      * inversion H_nth.
        exists 0.
        simpl.
        reflexivity.
      * assert (exists h' : nat, nth_error port_buf h' = Some (p, m', c'))
          by (eapply IHport_buf; eassumption).
        destruct H.
        exists (S x).
        simpl.
        assumption.
Qed.

Lemma extract_port_buffer_success_lookups_reveal_old:
  forall buf buf' l i j m c k h port_buf' p m' c',
  extract_port_buffer buf l i j m c = (buf', Some (j, i, m, c)) ->
  nth_error buf' k = Some port_buf' ->
  nth_error port_buf' h = Some (p, m', c') ->
  exists k' h' port_buf,
    (nth_error buf k' = Some port_buf /\
     nth_error port_buf h' = Some (p, m', c')).
Proof.
  intros buf.
  induction buf;
  intros buf' l i j m c k h port_buf' p m' c';
  intros H_extract H_nth_port_buf H_nth_mes.
  - inversion H_extract.
  - simpl in H_extract.
    destruct l.
    + destruct (extract_message a i j m c) eqn:mes.
      inversion H_extract.
      subst. clear H_extract.
      destruct k;
      simpl in H_nth_port_buf.
      * inversion H_nth_port_buf.
        subst. clear H_nth_port_buf.
        assert (exists h, nth_error a h = Some (p, m', c'))
          by (eapply extract_message_success_lookups_reveal_old;
              eassumption).
        inversion H.
        exists 0, x, a.
        split.
        -- simpl.
           reflexivity.
        -- assumption.
      * exists (S k), h, port_buf'.
        split;
        assumption.
    + destruct (extract_port_buffer buf l i j m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      destruct k;
      simpl in H_nth_port_buf.
      * inversion H_nth_port_buf.
        exists 0, h, port_buf'.
        split.
        -- simpl.
           reflexivity.
        -- assumption.
      * assert (exists (k' h' : nat) (port_buf : In_transit_port_buffer),
                  nth_error buf k' = Some port_buf /\ nth_error port_buf h' = Some (p, m', c'))
          by (eapply IHbuf; eassumption).
        do 3 destruct H.
        exists (S x), x0, x1.
        simpl.
        assumption.
Qed.

Lemma extract_message_success_reveal_message:
  forall port_buf port_buf' i j m c,
  extract_message port_buf i j m c = (port_buf', Some (j, i, m, c)) ->
  exists k, nth_error port_buf k = Some (i, m, c).
Proof.
  intros port_buf.
  induction port_buf;
  intros port_buf' i j m c;
  intros H_extract.
  - inversion H_extract.
  - simpl in H_extract.
    destruct a.
    destruct p.
    destruct (triple_and (Nat.eqb i n0) (m =? s)%string (Nat.eqb c n)) eqn:eq.
    + inversion H_extract.
      subst. clear H_extract.
      exists 0.
      simpl.
      unfold triple_and in eq.
      destruct (Nat.eqb i n0) eqn:eqi.
      * destruct ((m =? s)%string) eqn:eqm.
        -- destruct (Nat.eqb c n) eqn:eqc.
           ++ apply EqNat.beq_nat_true in eqi.
              apply eqb_eq in eqm.
              apply EqNat.beq_nat_true in eqc.
              subst.
              reflexivity.
           ++ discriminate.
        -- discriminate.
      * discriminate.
    + destruct (extract_message port_buf i j m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      assert (exists k : nat, nth_error port_buf k = Some (i, m, c))
        by (eapply IHport_buf; eassumption).
      destruct H.
      exists (S x).
      simpl.
      assumption.
Qed.

Lemma extract_port_buffer_success_reveal_message:
  forall buf buf' l i j m c,
  extract_port_buffer buf l i j m c = (buf', Some (j, i, m, c)) ->
  exists k h port_buf,
    (nth_error buf k = Some port_buf /\
     nth_error port_buf h = Some (i, m, c)).
Proof.
  intros buf.
  induction buf;
  intros buf' l i j m c;
  intros H_extract.
  - inversion H_extract.
  - simpl in H_extract.
    destruct l.
    + destruct (extract_message a i j m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      assert (exists k, nth_error a k = Some (i, m, c))
        by (eapply extract_message_success_reveal_message;
            eassumption).
      destruct H.
      exists 0, x, a.
      split.
      * simpl.
        reflexivity.
      * assumption.
    + destruct (extract_port_buffer buf l i j m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      assert (exists (k h : nat) (port_buf : In_transit_port_buffer),
                nth_error buf k = Some port_buf /\ nth_error port_buf h = Some (i, m, c))
        by (eapply IHbuf; eassumption).
      do 3 destruct H.
      exists (S x), x0, x1.
      simpl.
      assumption.
Qed.

Lemma extract_port_buffer_preserves_length:
  forall buf buf' i j j' m c res,
  extract_port_buffer buf j i j' m c = (buf', res) ->
  Datatypes.length buf = Datatypes.length buf'.
Proof.
  intros buf.
  induction buf;
  intros buf' i j j' m c res;
  intros H_extract;
  simpl.
  - simpl in H_extract.
    inversion H_extract.
    simpl.
    reflexivity.
  - simpl in H_extract.
    destruct j.
    + destruct (extract_message a i j' m c).
      inversion H_extract.
      simpl.
      reflexivity.
    + destruct (extract_port_buffer buf j i j' m c) eqn:extract.
      inversion H_extract.
      subst. clear H_extract.
      simpl.
      rewrite IHbuf with i0 i j j' m c res.
      * reflexivity.
      * assumption.
Qed.

Lemma extract_from_buffer_with_message_just_added_cannot_fail:
  forall buf i j j' m c,
  j < Datatypes.length buf ->
  exists buf' res, extract_port_buffer (add_message_to_all buf i m c) j i j' m c = (buf', Some res).
Proof.
  intros buf.
  induction buf;
  intros i j j' m c;
  intros H_le;
  simpl in H_le |- *.
  - inversion H_le.
  - destruct j.
    + destruct (triple_and (Nat.eqb i i) (m =? m)%string (Nat.eqb c c)) eqn:eq.
      * exists (a :: add_message_to_all buf i m c),
               (j', i, m, c).
        reflexivity.
      * unfold triple_and in eq.
        destruct (Nat.eqb i i) eqn:i_eq.
        -- destruct ((m =? m)%string) eqn:m_eq.
           ++ destruct (Nat.eqb c c) eqn:c_eq.
              ** inversion eq.
              ** apply EqNat.beq_nat_false in c_eq.
                 contradiction.
           ++ apply eqb_neq in m_eq.
              contradiction.
        -- apply EqNat.beq_nat_false in i_eq.
           contradiction.
    + destruct (extract_port_buffer (add_message_to_all buf i m c) j i j' m c) eqn:extract.
      assert (exists buf' res,
          extract_port_buffer (add_message_to_all buf i m c) j i j' m c = (buf', Some res))
        as H_extract_is_some
        by (apply IHbuf;
            apply Lt.lt_S_n;
            assumption).
      destruct H_extract_is_some as [buf' H_extract_is_some].
      destruct H_extract_is_some as [res H_extract_is_some].
      rewrite H_extract_is_some in extract.
      inversion extract.
      subst.
      exists (((i, m, c) :: a) :: i0), res.
      reflexivity.
Qed.

Lemma extract_port_buffer_out_of_bounds_implies_none:
  forall buf i j j' m c,
  Datatypes.length buf <= j ->
  extract_port_buffer buf j i j' m c = (buf, None).
Proof.
  intros buf.
  induction buf;
  intros i j j' m c;
  intros H_ge;
  simpl in H_ge.
  - simpl.
    reflexivity.
  - destruct j.
    + assert False
        as H_false
        by (eapply PeanoNat.Nat.nle_succ_0;
            eassumption).
      inversion H_false.
    + simpl.
      rewrite IHbuf.
      * reflexivity.
      * apply le_S_n.
        assumption.
Qed.
