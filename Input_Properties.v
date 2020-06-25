
Require Import String.

Import List.
Import ListNotations.

Require Import List_Properties.
Require Import Utilities.


Inductive input : Set :=
(* Send port_from (message, counter) *)
| Send    : nat -> (string * nat) -> input
(* Deliver port_from port_at (message, counter) *)
| Deliver : nat -> nat -> (string * nat) -> input.

Definition inputs : Type := list input.


Definition user_contract (order : inputs) : Prop :=
  forall i m1 m2 c1 c2 t1 t2,
  nth_error order t1 = Some (Send i (m1, c1)) ->
  nth_error order t2 = Some (Send i (m2, c2)) ->
  t1 <> t2 ->
  m1 <> m2.


Lemma user_contract_smaller_cons: forall inp i,
  user_contract (i :: inp) ->
  user_contract inp.
Proof.
  intros.
  unfold user_contract in * |- *.
  intros p m1 m2 c1 c2 t1 t2.
  intros H_nth1 H_nth2 H_t_ne.
  apply H with p c1 c2 (S t1) (S t2);
    simpl;
    try assumption.
  unfold not.
  intros H_eq.
  apply H_t_ne.
  inversion H_eq.
  reflexivity.
Qed.

Lemma user_contract_smaller_concat:
  forall inp inp',
  user_contract (inp ++ inp') ->
  user_contract inp.
Proof.
  intros inp inp' H_contract.
  unfold user_contract in * |- *.
  intros p m1 m2 c1 c2 t1 t2.
  intros H_nth1 H_nth2 H_t_ne.
  apply H_contract
    with p c1 c2 t1 t2;
    try apply nth_succes_larger;
    assumption.
Qed.

Lemma user_contract_smaller_append: forall inp i,
  user_contract (inp ++ [i]) ->
  user_contract inp.
Proof.
  intros.
  eapply user_contract_smaller_concat.
  eassumption.
Qed.

Lemma user_contract_double_send_implies_some_diff:
  forall inp i i' m m' c c' t t',
  user_contract inp ->
  nth_error inp t = Some (Send i (m, c)) ->
  nth_error inp t' = Some (Send i' (m', c')) ->
  t <> t' ->
  (i, m) <> (i', m').
Proof.
  intros inp i i' m m' c c' t t'.
  intros H_contract H_nth H_nth' H_diff_t.
  unfold user_contract in H_contract.
  unfold not.
  intros H_eq.
  inversion H_eq.
  subst. clear H_eq.
  assert (m' <> m')
    as H_m_ne
    by (eapply H_contract
          with (t1 := t) (t2 := t');
        eassumption).
  apply H_m_ne.
  reflexivity.
Qed.


(* n = number of parties *)
Definition input_liveness (inp: inputs) (n: nat) : Prop :=
  forall i m c t1,
  nth_error inp t1 = Some (Send i (m, c)) ->
  (forall j, j < n -> exists t2, t1 < t2 /\ nth_error inp t2 = Some (Deliver i j (m, c))).

Definition no_late_specific_send (inp : inputs) (t i : nat) (m : string) (c : nat) : Prop :=
  forall t' i' m' c',
  t < t' ->
  nth_error inp t' = Some (Send i' (m', c')) ->
  (i, m, c) <> (i', m', c').

Lemma no_late_specific_send_implies_shorter:
  forall inp inp' t i m c,
  no_late_specific_send (inp ++ inp') t i m c ->
  no_late_specific_send inp t i m c.
Proof.
  intros inp inp' t i m c.
  intros H_no_late_concat.
  unfold no_late_specific_send in * |- *.
  intros t' i' m' c'.
  intros H_t_le H_nth_send.
  eapply H_no_late_concat.
  - eassumption.
  - apply nth_succes_larger.
    eassumption.
Qed.

Lemma send_late_or_not_in_inp:
  forall inp i m c,
  (exists t, nth_error inp t = Some (Send i (m, c)) /\ no_late_specific_send inp t i m c) \/
  (forall t, nth_error inp t <> Some (Send i (m, c))).
Proof.
  intros inp.
  induction inp;
  intros i m c.
  - right.
    unfold not.
    intros t H_nth.
    nth_error_empty.
  - specialize (IHinp i m c).
    destruct IHinp as [H_earlier | H_no_send].
    + destruct H_earlier as [t H_earlier].
      destruct H_earlier as [H_nth_send H_no_send_later].
      left.
      exists (S t).
      split.
      * simpl.
        assumption.
      * unfold no_late_specific_send in * |- *.
        intros t' i' m' c''.
        intros H_t_le H_nth_diff_send.
        destruct t'.
        -- inversion H_t_le.
        -- apply H_no_send_later with t'.
           ++ apply Lt.lt_S_n.
              assumption.
           ++ simpl in H_nth_diff_send.
              assumption.
    + destruct a.
      * destruct p.
        assert ((i, c, m) = (n, n0, s) \/ (i, c, m) <> (n, n0, s))
          as H_the_send_or_not
          by (apply tuple_nat_nat_string_eq_dec).
        destruct H_the_send_or_not as [H_eq | H_ne].
        -- inversion H_eq.
           subst. clear H_eq.
           left.
           exists 0.
           split.
           ++ simpl.
              reflexivity.
           ++ unfold no_late_specific_send.
              intros t' i' m' c''.
              intros H_t_le H_nth_diff_send.
              destruct t'.
              ** inversion H_t_le.
              ** simpl in H_nth_diff_send.
                 unfold not.
                 intros H_eq.
                 inversion H_eq.
                 subst. clear H_eq.
                 specialize (H_no_send t').
                 contradiction.
        -- right.
           intros t.
           destruct t;
           simpl.
           ++ unfold not.
              intros H_eq.
              inversion H_eq.
              subst. clear H_eq.
              apply H_ne.
              reflexivity.
           ++ apply H_no_send.
      * right.
        intros t.
        destruct t;
        simpl.
        -- discriminate.
        -- apply H_no_send.
Qed.
