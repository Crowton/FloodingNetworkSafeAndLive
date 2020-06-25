
Require Import String.

Lemma nat_eq_dec:
  forall (i j : nat),
  i = j \/ i <> j.
Proof.
  intros i.
  induction i;
  intros j.
  - destruct j.
    + left.
      reflexivity.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
  - destruct j.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
    + specialize (IHi j).
      destruct IHi.
      * subst.
        left.
        reflexivity.
      * right.
        unfold not.
        intros H_eq.
        inversion H_eq.
        contradiction.
Qed.

Lemma ascii_eq_dec:
  forall (a b : Ascii.ascii),
  a = b \/ a <> b.
Proof.
  intros a b.
  destruct a as [a0 a1 a2 a3 a4 a5 a6 a7].
  destruct b as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct a0, b0;
  match goal with
  | [_ : _ |- Ascii.Ascii ?v0 _ _ _ _ _ _ _ = Ascii.Ascii ?v0 _ _ _ _ _ _ _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a1, b1;
  match goal with
  | [_ : _ |- Ascii.Ascii _ ?v1 _ _ _ _ _ _ = Ascii.Ascii _ ?v1 _ _ _ _ _ _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a2, b2;
  match goal with
  | [_ : _ |- Ascii.Ascii _ _ ?v2 _ _ _ _ _ = Ascii.Ascii _ _ ?v2 _ _ _ _ _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a3, b3;
  match goal with
  | [_ : _ |- Ascii.Ascii _ _ _ ?v3 _ _ _ _ = Ascii.Ascii _ _ _ ?v3 _ _ _ _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a4, b4;
  match goal with
  | [_ : _ |- Ascii.Ascii _ _ _ _ ?v4 _ _ _ = Ascii.Ascii _ _ _ _ ?v4 _ _ _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a5, b5;
  match goal with
  | [_ : _ |- Ascii.Ascii _ _ _ _ _ ?v5 _ _ = Ascii.Ascii _ _ _ _ _ ?v5 _ _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a6, b6;
  match goal with
  | [_ : _ |- Ascii.Ascii _ _ _ _ _ _ ?v6 _ = Ascii.Ascii _ _ _ _ _ _ ?v6 _ \/ _ ] =>
      simpl
  | _ =>
      right;
      unfold not;
      intros H_eq;
      inversion H_eq
  end;
  destruct a7, b7;
  try (left;
       reflexivity);
  right;
  unfold not;
  intros H_eq;
  inversion H_eq.
Qed.

Lemma string_eq_dec:
  forall (s m : string),
  s = m \/ s <> m.
Proof.
  intros s.
  induction s;
  intros m.
  - destruct m.
    + left.
      reflexivity.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
  - destruct m.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
    + specialize (IHs m).
      destruct IHs.
      * subst.
        assert (a = a0 \/ a <> a0)
          as H_a_eq_dec
          by (apply ascii_eq_dec).
        destruct H_a_eq_dec as [H_a_eq | H_a_not_eq].
        -- subst.
           left.
           reflexivity.
        -- right.
           unfold not.
           intros H_eq.
           inversion H_eq.
           contradiction.
      * right.
        unfold not.
        intros H_eq.
        inversion H_eq.
        contradiction.
Qed.

Lemma tuple_nat_string_eq_dec:
  forall (i i' : nat) (m m' : string),
  (i, m) = (i', m') \/ (i, m) <> (i', m').
Proof.
  intros.
  assert (i = i' \/ i <> i')
    as H_i_eq_dec
    by (apply nat_eq_dec).
  destruct H_i_eq_dec as [H_i_eq | H_i_not_eq].
  - subst.
    assert (m = m' \/ m <> m')
      as H_m_eq_dec
      by (apply string_eq_dec).
    destruct H_m_eq_dec as [H_m_eq | H_m_not_eq].
    + subst.
      left.
      reflexivity.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
      contradiction.
  - right.
    unfold not.
    intros H_eq.
    inversion H_eq.
    contradiction.
Qed.

Lemma tuple_nat_nat_string_eq_dec:
  forall (i i' j j' : nat) (m m' : string),
  (i, j, m) = (i', j', m') \/ (i, j, m) <> (i', j', m').
Proof.
  intros.
  assert (i = i' \/ i <> i')
    as H_i_eq_dec
    by (apply nat_eq_dec).
  destruct H_i_eq_dec as [H_i_eq | H_i_not_eq].
  - subst.
    assert (j = j' \/ j <> j')
      as H_j_eq_dec
      by (apply nat_eq_dec).
    destruct H_j_eq_dec as [H_j_eq | H_j_not_eq].
    + assert (m = m' \/ m <> m')
        as H_m_eq_dec
        by (apply string_eq_dec).
      destruct H_m_eq_dec as [H_m_eq | H_m_not_eq].
      * subst.
        left.
        reflexivity.
      * right.
        unfold not.
        intros H_eq.
        inversion H_eq.
        contradiction.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
      contradiction.
  - right.
    unfold not.
    intros H_eq.
    inversion H_eq.
    contradiction.
Qed.

Lemma tuple_nat_string_nat_eq_dec:
  forall (i i' : nat) (m m': string) (c c' : nat),
  (i, m, c) = (i', m', c') \/ (i, m, c) <> (i', m', c').
Proof.
  intros i i' m m' c c'.
  assert ((i, c, m) = (i', c', m') \/ (i, c, m) <> (i', c', m'))
    as H_dec_eq_swapped
    by (apply tuple_nat_nat_string_eq_dec).
  destruct H_dec_eq_swapped as [H_eq | H_not_eq].
  - inversion H_eq.
    left.
    reflexivity.
  - right.
    unfold not.
    intros H_eq.
    inversion H_eq.
    subst. clear H_eq.
    apply H_not_eq.
    reflexivity.
Qed.

Lemma tuple_nat_nat_string_nat_eq_dec:
  forall (i i' j j' : nat) (m m' : string) (c c' : nat),
  (i, j, m, c) = (i', j', m', c') \/ (i, j, m, c) <> (i', j', m', c').
Proof.
  intros.
  assert ((i, j, m) = (i', j', m') \/ (i, j, m) <> (i', j', m'))
    as H_dec_eq_first
    by (apply tuple_nat_nat_string_eq_dec).
  destruct H_dec_eq_first as [H_eq | H_not_eq].
  - inversion H_eq.
    subst. clear H_eq.
    assert (c = c' \/ c <> c')
      as H_c_eq_dec
      by (apply nat_eq_dec).
    destruct H_c_eq_dec as [H_c_eq | H_c_not_eq].
    + subst.
      left.
      reflexivity.
    + right.
      unfold not.
      intros H_eq.
      inversion H_eq.
      contradiction.
  - right.
    unfold not.
    intros H_eq.
    inversion H_eq.
    subst.
    contradiction.
Qed.

Lemma tuple_nat_string_nat_not_eq_implies_or:
  forall (i i' : nat) (m m': string) (c c' : nat),
  (i, m, c) <> (i', m', c') ->
  i <> i' \/ m <> m' \/ c <> c'.
Proof.
  intros i i' m m' c c'.
  intros H_not.
  assert (i = i' \/ i <> i')
    as H_i_eq_dec
    by (apply nat_eq_dec).
  destruct H_i_eq_dec.
  - subst.
    assert (m = m' \/ m <> m')
      as H_m_eq_dec
      by (apply string_eq_dec).
    destruct H_m_eq_dec.
    + subst.
      assert (c = c' \/ c <> c')
        as H_c_eq_dec
        by (apply nat_eq_dec).
      destruct H_c_eq_dec.
      * subst.
        contradiction.
      * right.
        right.
        assumption.
    + right.
      left.
      assumption.
  - left.
    assumption.
Qed.
