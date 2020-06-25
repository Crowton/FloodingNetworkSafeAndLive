
Require Import String.
Import List.
Import ListNotations.

Require Import Flood_Properties.
Require Import List_Properties.


(* Not needed but it's sanity *)
Lemma flood_safety_concat:
  forall trace trace',
  flood_safety trace ->
  flood_safety trace' ->
  flood_safety (trace ++ trace').
Proof.
  unfold flood_safety.
  intros.
  apply nth_index_in_concat in H1.
  destruct H1.
  - assert (exists t1 : nat, t1 < t2 /\ nth_error trace t1 = Some (Flood_Input i (m, c))).
    + eapply H.
      eassumption.
    + destruct H2.
      exists x.
      destruct H2.
      split.
      * assumption.
      * rewrite nth_error_app1.
        -- assumption.
        -- apply nth_error_Some.
           rewrite H3.
           discriminate.
  - destruct H1.
    destruct H1.
    assert (exists t1 : nat, t1 < x /\ nth_error trace' t1 = Some (Flood_Input i (m, c))).
    + eapply H0.
      eassumption.
    + destruct H3.
      destruct H3.
      exists (x0 + Datatypes.length trace).
      split.
      * rewrite <- H1.
        apply Plus.plus_lt_compat_r.
        assumption.
      * rewrite nth_error_app2.
        -- rewrite PeanoNat.Nat.add_sub.
           assumption.
        -- apply Plus.le_plus_r.
Qed.


Lemma flood_safety_append_not_output: forall trace t,
  flood_safety trace ->
  (forall i j m c, t <> Flood_Output i j (m, c)) ->
  flood_safety (trace ++ [t]).
Proof.
  intros trace t.
  unfold flood_safety in * |- *.
  intros H_trace_safety H_not_output.
  intros i j m c t2 H_nth.
  specialize (H_trace_safety i j m c t2).
  assert (exists t1 : nat, t1 < t2 /\ nth_error trace t1 = Some (Flood_Input i (m, c))).
  - apply H_trace_safety.
    apply nth_different_tail_smaller with t.
    + apply H_not_output.
    + assumption.
  - destruct H as [t1 H].
    destruct H.
    exists t1.
    split.
    + assumption.
    + apply nth_succes_larger.
      assumption.
Qed.


Lemma flood_safety_append_input: forall trace i m c,
  flood_safety trace ->
  flood_safety (trace ++ [Flood_Input i (m, c)]).
Proof.
  intros.
  apply flood_safety_append_not_output.
  assumption.
  intros.
  discriminate.
Qed.

Lemma flood_safety_append_leak: forall trace i m c,
  flood_safety trace ->
  flood_safety (trace ++ [Flood_Leak i (m, c)]).
Proof.
  intros.
  apply flood_safety_append_not_output.
  assumption.
  intros.
  discriminate.
Qed.

Lemma flood_safety_append_deliver: forall trace i j m c,
  flood_safety trace ->
  flood_safety (trace ++ [Flood_Deliver i j (m, c)]).
Proof.
  intros.
  apply flood_safety_append_not_output.
  assumption.
  intros.
  discriminate.
Qed.

Lemma flood_safety_append_output:
  forall trace t i j m c,
  flood_safety trace ->
  nth_error trace t = Some (Flood_Input i (m, c)) ->
  flood_safety (trace ++ [Flood_Output i j (m, c)]).
Proof.
  intros trace t i j m c.
  intros H_safe_trace H_nth_input.
  unfold flood_safety in * |- *.
  intros i' j' m' c' t2.
  intros H_nth_output.
  assert (t2 < Datatypes.length trace \/ Datatypes.length trace <= t2)
    as H_t2_lt_ge
    by (apply PeanoNat.Nat.lt_ge_cases).
  destruct H_t2_lt_ge as [H_t2_lt | H_t2_ge].
  - assert (nth_error trace t2 = Some (Flood_Output i' j' (m', c'))).
    + erewrite <- nth_error_app1;
      eassumption.
    + assert (exists t1 : nat, t1 < t2 /\ nth_error trace t1 = Some (Flood_Input i' (m', c')))
        as H_input_in_trace
        by (eapply H_safe_trace;
            try eassumption).
      destruct H_input_in_trace as [t1 H_input_in_trace].
      destruct H_input_in_trace as [H_t1_lt H_input_in_trace].
      exists t1.
      split.
      * assumption.
      * rewrite nth_error_app1.
        -- assumption.
        -- eapply PeanoNat.Nat.lt_trans;
           eassumption.
  - rewrite nth_error_app2 in H_nth_output.
    + exists t.
      split.
      * assert (t < Datatypes.length trace).
        -- apply nth_error_Some.
           unfold not.
           intros H_is_none.
           rewrite H_is_none in H_nth_input.
           discriminate.
        -- eapply PeanoNat.Nat.lt_le_trans;
           eassumption.
      * apply nth_succes_larger.
        assert (t2 - Datatypes.length trace < Datatypes.length [Flood_Output i j (m, c)])
          as H_t2_lt_length.
        -- apply nth_error_Some.
           unfold not.
           intros H_is_none.
           rewrite H_is_none in H_nth_output.
           discriminate.
        -- simpl in H_t2_lt_length.
           destruct (t2 - Datatypes.length trace).
           ++ simpl in H_nth_output.
              inversion H_nth_output.
              subst. clear H_nth_output.
              assumption.
           ++ inversion H_t2_lt_length.
              apply Le.le_n_0_eq in H0.
              inversion H0.
    + assumption.
Qed.
