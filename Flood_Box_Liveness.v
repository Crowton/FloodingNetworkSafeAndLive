
Require Import String.
Import List.
Import ListNotations.

Require Import Utilities.

Require Import Input_Properties.
Require Import Flood_Properties.
Require Import Flood_Box.

Require Import List_Properties.

Require Import extract_port_buffer_message_properties.
Require Import execute_flood_aux_properties.



Lemma fail_on_add_diff_message_implies_fails_before:
  forall buf buf' i i' j j' m m' c c',
  extract_port_buffer (add_message_to_all buf i' m' c') j i j' m c = (buf', None) ->
  (i', m', c') <> (i, m, c) ->
  exists buf'', extract_port_buffer buf j i j' m c = (buf'', None).
Proof.
  intros buf.
  induction buf;
  intros buf' i i' j j' m m' c c';
  intros H_extract_add H_ne.
  - simpl.
    exists [].
    reflexivity.
  - simpl in H_extract_add |- *.
    destruct j.
    + destruct (triple_and (Nat.eqb i i') (m =? m')%string (Nat.eqb c c')) eqn:and_eq.
      * apply tuple_nat_string_nat_not_eq_implies_or in H_ne.
        destruct H_ne.
        -- apply PeanoNat.Nat.eqb_neq in H.
           destruct (Nat.eqb i i') eqn:rem.
           ++ rewrite PeanoNat.Nat.eqb_sym in H.
              rewrite rem in H.
              discriminate.
           ++ unfold triple_and in and_eq.
              discriminate.
        -- destruct H.
           ++ apply eqb_neq in H.
              rewrite eqb_sym in H.
              rewrite H in and_eq.
              unfold triple_and in and_eq.
              destruct (Nat.eqb i i');
              discriminate.
           ++ apply PeanoNat.Nat.eqb_neq in H.
              destruct (Nat.eqb c c') eqn:rem.
              ** rewrite PeanoNat.Nat.eqb_sym in H.
                 rewrite rem in H.
                 discriminate.
              ** unfold triple_and in and_eq.
                 discriminate.
      * destruct (extract_message a i j' m c).
        inversion H_extract_add.
        exists (i0 :: buf).
        reflexivity.
    + destruct (extract_port_buffer (add_message_to_all buf i' m' c') j i j' m c) eqn:extract.
      inversion H_extract_add.
      subst. clear H_extract_add.
      assert (exists buf'' : In_transit_buffer, extract_port_buffer buf j i j' m c = (buf'', None))
        as H_extract_is_none
        by (eapply IHbuf;
            eassumption).
      destruct H_extract_is_none as [buf'' H_extract_is_none].
      exists (a :: buf'').
      rewrite H_extract_is_none.
      reflexivity.
Qed.



Lemma fail_on_extract_message_diff_message_implies_fails_before:
  forall port_buf port_buf' port_buf'' i i' j j' m m' c c' res,
  extract_message port_buf i' j' m' c' = (port_buf', res) ->
  extract_message port_buf' i j m c = (port_buf'', None) ->
  (i', m', c') <> (i, m, c) ->
  exists some_port_buf, extract_message port_buf i j m c = (some_port_buf, None).
Proof.
  intros port_buf.
  induction port_buf;
  intros port_buf' port_buf'' i i' j j' m m' c c' res;
  intros H_extract_first H_extract H_ne.
  - exists [].
    simpl.
    reflexivity.
  - simpl in H_extract_first |- *.
    destruct a.
    destruct p.
    destruct (triple_and (Nat.eqb i' n0) (m' =? s)%string (Nat.eqb c' n)) eqn:and_first.
    + destruct (triple_and (Nat.eqb i n0) (m =? s)%string (Nat.eqb c n)) eqn:and_second.
      * unfold triple_and in and_first, and_second.
        destruct (Nat.eqb i' n0) eqn:H_i'n0;
        destruct ((m' =? s)%string) eqn:H_m's;
        destruct (Nat.eqb c' n) eqn:H_c'n;
        destruct (Nat.eqb i n0) eqn:H_in0;
        destruct ((m =? s)%string) eqn:H_ms;
        destruct (Nat.eqb c n) eqn:H_cn;
          try discriminate.
        clear and_first. clear and_second.
        apply EqNat.beq_nat_true in H_i'n0.
        apply EqNat.beq_nat_true in H_in0.
        apply eqb_eq in H_m's.
        apply eqb_eq in H_ms.
        apply EqNat.beq_nat_true in H_c'n.
        apply EqNat.beq_nat_true in H_cn.
        subst.
        contradiction.
      * inversion H_extract_first.
        subst. clear H_extract_first.
        rewrite H_extract.
        exists ((n0, s, n) :: port_buf'').
        reflexivity.
    + destruct (extract_message port_buf i' j' m' c') eqn:extract_first.
      inversion H_extract_first.
      subst. clear H_extract_first.
      destruct (triple_and (Nat.eqb i n0) (m =? s)%string (Nat.eqb c n)) eqn:and_second;
      simpl in H_extract;
      rewrite and_second in H_extract.
      * inversion H_extract.
      * destruct (extract_message i0 i j m c) eqn:extract_second.
        inversion H_extract.
        subst. clear H_extract.
        assert (exists some_port_buf, extract_message port_buf i j m c = (some_port_buf, None))
          as H_must_fail
          by (eapply IHport_buf;
              eassumption).
        destruct H_must_fail as [some_port_buf H_must_fail].
        rewrite H_must_fail.
        exists ((n0, s, n) :: some_port_buf).
        reflexivity.
Qed.

Lemma fail_on_extract_port_buffer_same_port_implies_fail_before:
  forall buf buf' buf'' i i' j' jp jp' m m' c c' p,
  extract_port_buffer buf j' i' jp' m' c' = (buf', Some p) ->
  extract_port_buffer buf' j' i jp m c = (buf'', None) ->
  (i', m', c') <> (i, m, c) ->
  exists some_buf, extract_port_buffer buf j' i jp m c = (some_buf, None).
Proof.
  intros buf.
  induction buf;
  intros buf' buf'' i i' j' jp jp' m m' c c' p;
  intros H_extract_some H_extract_none H_diff;
  simpl in H_extract_some |- * .
  - inversion H_extract_some.
  - destruct j'.
    + destruct (extract_message a i' jp' m' c') eqn:extract_mes_some.
      inversion H_extract_some.
      subst. clear H_extract_some.
      simpl in H_extract_none.
      destruct (extract_message i0 i jp m c) eqn:extract_mes_none.
      inversion H_extract_none.
      subst. clear H_extract_none.
      assert (exists some_port_buf, extract_message a i jp m c = (some_port_buf, None))
        as H_res_none
        by (eapply fail_on_extract_message_diff_message_implies_fails_before;
            eassumption).
      destruct H_res_none as [some_port_buf H_res_none].
      rewrite H_res_none.
      exists (some_port_buf :: buf).
      reflexivity.
    + destruct (extract_port_buffer buf j' i' jp' m' c') eqn:extract_some.
      inversion H_extract_some.
      subst. clear H_extract_some.
      simpl in H_extract_none.
      destruct (extract_port_buffer i0 j' i jp m c) eqn:extract_none.
      inversion H_extract_none.
      subst. clear H_extract_none.
      assert (exists some_buf, extract_port_buffer buf j' i jp m c = (some_buf, None))
        as H_res_none
        by (eapply IHbuf;
            eassumption).
      destruct H_res_none as [some_buf H_res_none].
      rewrite H_res_none.
      exists (a :: some_buf).
      reflexivity.
Qed.

Lemma fail_on_extract_port_buffer_diff_port_implies_fail_before:
  forall buf buf' buf'' i i' j j' jp jp' m m' c c' p,
  extract_port_buffer buf j' i' jp' m' c' = (buf', Some p) ->
  extract_port_buffer buf' j i jp m c = (buf'', None) ->
  j <> j' ->
  exists some_buf, extract_port_buffer buf j i jp m c = (some_buf, None).
Proof.
  intros buf.
  induction buf;
  intros buf' buf'' i i' j j' jp jp' m m' c c' p;
  intros H_extract_first H_extract_fail H_ne;
  simpl in H_extract_first |- *.
  - inversion H_extract_first.
  - destruct j'.
    + destruct (extract_message a i' jp' m' c') eqn:extract_mes_first.
      inversion H_extract_first.
      subst. clear H_extract_first.
      simpl in H_extract_fail.
      destruct j.
      * contradiction.
      * destruct (extract_port_buffer buf j i jp m c) eqn:extract_second.
        inversion H_extract_fail.
        subst. clear H_extract_fail.
        exists (a :: i1).
        reflexivity.
    + destruct (extract_port_buffer buf j' i' jp' m' c') eqn:extract_first.
      inversion H_extract_first.
      subst. clear H_extract_first.
      simpl in H_extract_fail.
      destruct j.
      * destruct (extract_message a i jp m c) eqn:extract_mes_second.
        inversion H_extract_fail.
        subst. clear H_extract_fail.
        exists (i1 :: buf).
        reflexivity.
      * destruct (extract_port_buffer i0 j i jp m c) eqn:extract_second.
        inversion H_extract_fail.
        subst. clear H_extract_fail.
        assert (exists some_buf, extract_port_buffer buf j i jp m c = (some_buf, None))
          as H_must_fail
          by (eapply IHbuf;
              try apply PeanoNat.Nat.succ_inj_wd_neg;
              eassumption).
        destruct H_must_fail as [some_buf H_must_fail].
        rewrite H_must_fail.
        exists (a :: some_buf).
        reflexivity.
Qed.

Lemma fail_on_extract_diff_message_implies_fails_before:
  forall buf buf' buf'' i i' j jp j' jp' m m' c c' res,
  extract_port_buffer buf j' i' jp' m' c' = (buf', res) ->
  extract_port_buffer buf' j i jp m c = (buf'', None) ->
  (i', j', m', c') <> (i, j, m, c) ->
  exists some_buf, extract_port_buffer buf j i jp m c = (some_buf, None).
Proof.
  intros buf buf' buf'' i i' j jp j' jp' m m' c c' res.
  intros H_extract_prev H_extract_fail H_ne.
  destruct res.
  - assert (j < Datatypes.length buf \/ Datatypes.length buf <= j)
      as H_out_of_bounds_or_not
      by (apply PeanoNat.Nat.lt_ge_cases).
    destruct H_out_of_bounds_or_not as [H_in_bounds | H_out_bounds].
    + assert (j = j' \/ j <> j')
        as H_j_eq_dec
        by (apply nat_eq_dec).
      destruct H_j_eq_dec as [H_j_eq | H_j_not_eq].
      * subst.
        eapply fail_on_extract_port_buffer_same_port_implies_fail_before;
          try eassumption.
        unfold not.
        intros H_eq.
        inversion H_eq.
        subst.
        apply H_ne.
        reflexivity.
      * eapply fail_on_extract_port_buffer_diff_port_implies_fail_before;
        eassumption.
    + apply extract_port_buffer_out_of_bounds_implies_none
        with buf i j jp m c
        in H_out_bounds.
      exists buf.
      assumption.
  - apply extract_port_buffer_none_action_same_buffer in H_extract_prev.
    subst.
    exists buf''.
    assumption.
Qed.


Definition input_message_then_fail_extract_implies_earlier_deliver_def
  (inp : inputs) : Prop :=
  forall t1 n i j m c trace buf buf',
  nth_error inp t1 = Some (Send i (m, c)) ->
  execute_flood_rec inp (Flood_Box_init n) = (trace, buf) ->
  extract_port_buffer buf j i j m c = (buf', None) ->
  j < n ->
  exists t2, t1 < t2 /\ nth_error inp t2 = Some (Deliver i j (m, c)).

Lemma input_message_then_fail_extract_implies_earlier_deliver:
  forall inp,
  input_message_then_fail_extract_implies_earlier_deliver_def inp.
Proof.
  apply rev_ind;
  unfold input_message_then_fail_extract_implies_earlier_deliver_def.
  - intros.
    nth_error_empty.
  - intros action inp.
    intros IHinp.
    intros t1 n i j m c trace buf buf'.
    intros H_inp_send H_exec H_extract_fail H_jle.
    apply concat_inp_concats_trace_split in H_exec.
    destruct H_exec as [buf_inter H_exec].
    destruct H_exec as [trace_head H_exec].
    destruct H_exec as [trace_tail H_exec].
    destruct H_exec as [H_trace_concat H_exec].
    destruct H_exec as [H_exec_inp H_exec_send].
    apply nth_index_in_concat in H_inp_send.
    destruct H_inp_send as [H_inp_send | H_inp_send_tail].
    + destruct action;
      simpl in H_exec_send.
      * destruct p.
        inversion H_exec_send.
        subst. clear H_exec_send.
        assert ((n0, s, n1) = (i, m, c) \/ (n0, s, n1) <> (i, m, c))
          as H_same_or_diff_send_params
          by (apply tuple_nat_string_nat_eq_dec).
        destruct H_same_or_diff_send_params as [H_same_params | H_diff_params].
        -- inversion H_same_params.
           subst. clear H_same_params.
           assert (n = Datatypes.length buf_inter)
             as H_buf_length
             by (rewrite <- length_of_flood_init_is_param with (n := n);
                 eapply execute_inp_preserves_buffer_length;
                 eassumption).
           subst.
           assert (exists buf' res,
                    extract_port_buffer (add_message_to_all buf_inter i m c) j i j m c
                      = (buf', Some res))
             as H_extract_not_fail
             by (apply extract_from_buffer_with_message_just_added_cannot_fail;
                 assumption).
           destruct H_extract_not_fail as [buf'' H_extract_not_fail].
           destruct H_extract_not_fail as [res H_extract_not_fail].
           rewrite H_extract_not_fail in H_extract_fail.
           inversion H_extract_fail.
        -- assert (exists buf', extract_port_buffer buf_inter j i j m c = (buf', None))
             as H_extract_smaller_fail
             by (eapply fail_on_add_diff_message_implies_fails_before;
                 eassumption).
           destruct H_extract_smaller_fail as [some_buf H_extract_smaller_fail].
           assert (exists t2 : nat, t1 < t2 /\ nth_error inp t2 = Some (Deliver i j (m, c)))
           as H_deliver_in_inp
           by (eapply IHinp;
               eassumption).
           destruct H_deliver_in_inp as [t2 H_deliver_in_inp].
           destruct H_deliver_in_inp as [H_le H_deliver_in_inp].
           exists t2.
           split.
           ++ assumption.
           ++ apply nth_succes_larger.
              assumption.
      * destruct p.
        assert ((n0, n1, s, n2) = (i, j, m, c) \/ (n0, n1, s, n2) <> (i, j, m, c))
          as H_same_or_diff_deliver_params
          by (apply tuple_nat_nat_string_nat_eq_dec).
        destruct H_same_or_diff_deliver_params as [H_same_params | H_diff_params].
        -- inversion H_same_params.
           subst. clear H_same_params.
           exists (Datatypes.length inp).
           split.
           ++ apply nth_error_Some.
              unfold not.
              intros H_none.
              rewrite H_none in H_inp_send.
              discriminate.
           ++ rewrite nth_error_app2.
              ** rewrite PeanoNat.Nat.sub_diag.
                 simpl.
                 reflexivity.
              ** apply PeanoNat.Nat.le_refl.
        -- destruct (extract_port_buffer buf_inter n1 n0 n1 s n2) eqn:del_extract.
           destruct o;
           try (do 3 destruct p);
           inversion H_exec_send;
           subst; clear H_exec_send;
           assert (exists buf', extract_port_buffer buf_inter j i j m c = (buf', None))
             as H_extract_smaller_fail
             by (eapply fail_on_extract_diff_message_implies_fails_before;
                 eassumption);
           destruct H_extract_smaller_fail as [some_buf H_extract_smaller_fail];
           assert (exists t2 : nat, t1 < t2 /\ nth_error inp t2 = Some (Deliver i j (m, c)))
           as H_deliver_in_inp
           by (eapply IHinp;
               eassumption);
           destruct H_deliver_in_inp as [t2 H_deliver_in_inp];
           destruct H_deliver_in_inp as [H_le H_deliver_in_inp];
           exists t2;
           split;
           try (apply nth_succes_larger);
           assumption.
    + destruct H_inp_send_tail as [offset H_inp_send_tail].
      destruct H_inp_send_tail as [H_offset H_inp_send_tail].
      destruct offset;
      simpl in H_inp_send_tail.
      * inversion H_inp_send_tail.
        subst. clear H_inp_send_tail.
        simpl in H_exec_send.
        inversion H_exec_send.
        subst. clear H_exec_send.
        assert (n = Datatypes.length buf_inter)
          as H_buf_length
          by (rewrite <- length_of_flood_init_is_param with (n := n);
              eapply execute_inp_preserves_buffer_length;
              eassumption).
        subst.
        assert (exists buf' res,
                 extract_port_buffer (add_message_to_all buf_inter i m c) j i j m c
                   = (buf', Some res))
          as H_extract_not_fail
          by (apply extract_from_buffer_with_message_just_added_cannot_fail;
              assumption).
        destruct H_extract_not_fail as [buf'' H_extract_not_fail].
        destruct H_extract_not_fail as [res H_extract_not_fail].
        rewrite H_extract_not_fail in H_extract_fail.
        inversion H_extract_fail.
      * nth_error_empty.
Qed.



Definition send_then_deliver_inp_implies_input_output_pair_in_trace_def
  (inp : inputs) : Prop :=
  forall t1 t1' t2 n i j m c trace buf,
  nth_error inp t1 = Some (Send i (m, c)) ->
  nth_error inp t2 = Some (Deliver i j (m, c)) ->
  t1 < t2 ->
  no_late_specific_send inp t1 i m c ->
  execute_flood_rec inp (Flood_Box_init n) = (trace, buf) ->
  nth_error trace t1' = Some (Flood_Input i (m, c)) ->
  j < n ->
  exists t2', t1' < t2' /\ nth_error trace t2' = Some (Flood_Output i j (m, c)).

Lemma send_then_deliver_inp_implies_input_output_pair_in_trace:
  forall inp,
  send_then_deliver_inp_implies_input_output_pair_in_trace_def inp.
Proof.
  apply rev_ind;
  unfold send_then_deliver_inp_implies_input_output_pair_in_trace_def.
  - intros.
    nth_error_empty.
  - intros action inp.
    intros IHinp.
    intros t1 t1' t2 n i j m c trace buf'.
    intros H_inp_send H_inp_deliver H_t_le H_inp_no_late_send H_exec H_trace_input H_port_exists.
    apply concat_inp_concats_trace_split in H_exec.
    destruct H_exec as [buf H_exec].
    destruct H_exec as [trace_head H_exec].
    destruct H_exec as [trace_tail H_exec].
    destruct H_exec as [trace_concat H_exec].
    destruct H_exec as [exec_inp exec_action].
    apply nth_index_in_concat in H_inp_send.
    destruct H_inp_send as [H_inp_send_head | H_inp_send_tail].
    + apply nth_index_in_concat in H_inp_deliver.
      destruct H_inp_deliver as [H_inp_deliver_head | H_inp_deliver_tail].
      * rewrite trace_concat in H_trace_input.
        assert (exists t2' : nat, t1' < t2' /\
                  nth_error trace_head t2' = Some (Flood_Output i j (m, c)))
          as H_output_in_head
          by (eapply IHinp;
              try eapply no_late_specific_send_implies_shorter;
              try eapply send_in_inp_head_implies_send_in_trace_head;
              eassumption).
        destruct H_output_in_head as [t2' H_output_in_head].
        destruct H_output_in_head as [H_le_prime H_output_in_head].
        exists t2'.
        split.
        -- assumption.
        -- rewrite trace_concat.
           eapply nth_succes_larger.
           eassumption.
      * destruct H_inp_deliver_tail as [offset H_inp_deliver_tail].
        destruct H_inp_deliver_tail as [H_offset H_inp_deliver_tail].
        destruct offset;
        simpl in H_inp_deliver_tail.
        -- inversion H_inp_deliver_tail.
           subst. clear H_inp_deliver_tail.
           simpl in H_t_le.
           simpl in exec_action.
           destruct (extract_port_buffer buf j i j m c) eqn:extract.
           destruct o.
           ++ do 3 destruct p.
              inversion exec_action.
              subst. clear exec_action.
              apply extract_port_buffer_success_same_output in extract.
              destruct extract as [H_eq1 H_eq].
              destruct H_eq as [H_j_eq H_eq].
              destruct H_eq as [H_m_eq H_c_eq].
              subst.
              exists (S (Datatypes.length trace_head)).
              split.
              ** apply nth_error_concat_not_in_tail_implies_head in H_trace_input.
                 --- apply PeanoNat.Nat.lt_lt_succ_r.
                     apply nth_error_Some.
                     unfold not.
                     intros H_none.
                     rewrite H_none in H_trace_input.
                     inversion H_trace_input.
                 --- unfold not.
                     intros H_in.
                     inversion H_in;  (* fix name, to be constant - match goal? *)
                     inversion H;
                     inversion H0.
              ** rewrite nth_error_app2.
                 --- rewrite <- Minus.minus_Sn_m.
                     +++ rewrite PeanoNat.Nat.sub_diag.
                         simpl.
                         reflexivity.
                     +++ apply PeanoNat.Nat.le_refl.
                 --- apply PeanoNat.Nat.le_succ_diag_r.
           ++ inversion exec_action.
              subst. clear exec_action.
              assert (exists t2, t1 < t2 /\ nth_error inp t2 = Some (Deliver i j (m, c)))
                as H_earlier_deliver
                by (eapply input_message_then_fail_extract_implies_earlier_deliver;
                    eassumption).
              destruct H_earlier_deliver as [t2 H_earlier_deliver].
              destruct H_earlier_deliver as [H_t1_le_t2 H_inp_deliver].
              assert (exists t2' : nat, t1' < t2' /\
                        nth_error trace_head t2' = Some (Flood_Output i j (m, c)))
                as H_output_in_head
                by (eapply IHinp;
                    try eassumption;
                    try eapply no_late_specific_send_implies_shorter;
                    try eapply nth_different_tail_smaller;
                    try eassumption;
                    discriminate).
              destruct H_output_in_head as [t2' H_output_in_head].
              destruct H_output_in_head as [H_le H_output_in_head].
              exists t2'.
              split.
              ** assumption.
              ** eapply nth_succes_larger.
                 eassumption.
        --  nth_error_empty.
    + destruct H_inp_send_tail as [offset H_inp_send_tail].
      destruct H_inp_send_tail as [H_offset H_inp_send_tail].
      destruct offset;
      simpl in H_inp_send_tail.
      * inversion H_inp_send_tail.
        simpl in H_offset.
        subst. clear H_inp_send_tail.
        apply nth_different_tail_smaller in H_inp_deliver.
        -- apply PeanoNat.Nat.lt_le_incl in H_t_le.
           apply nth_error_None in H_t_le.
           rewrite H_inp_deliver in H_t_le.
           inversion H_t_le.
        -- unfold not.
           intros H_err.
           inversion H_err.
      * nth_error_empty.
Qed.


Theorem Flood_Box_Liveness:
  forall inp n trace,
  user_contract inp ->
  input_liveness inp n ->
  execute_flood inp n = trace ->
  flood_liveness trace n.
Proof.
  intros inp n trace.
  intros H_contract H_live_inp H_exec.
  unfold flood_liveness.
  intros i m c t1.
  intros H_nth j H_in.
  unfold execute_flood in H_exec.
  destruct (execute_flood_rec inp (Flood_Box_init n)) eqn:exec_rec.
  simpl in H_exec.
  subst.
  assert (exists t1', nth_error inp t1' = Some (Send i (m, c))/\
                      no_late_specific_send inp t1' i m c)
    as H_inp_send
    by (eapply input_in_trace_implies_late_send_in_inp;
        eassumption).
  destruct H_inp_send as [t1' H_inp_send].  
  destruct H_inp_send as [H_inp_send H_inp_late_non_send].
  unfold input_liveness in H_live_inp.
  assert (exists t2 : nat, t1' < t2 /\ nth_error inp t2 = Some (Deliver i j (m, c)))
    as H_deliver_inp
    by (eapply H_live_inp;
        eassumption).
  destruct H_deliver_inp as [t2 H_deliver_inp].
  destruct H_deliver_inp as [H_t_le H_deliver_inp].
  eapply send_then_deliver_inp_implies_input_output_pair_in_trace;
  eassumption.
Qed.
