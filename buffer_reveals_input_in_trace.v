
Require Import String.
Import List.
Import ListNotations.

Require Import Input_Properties.
Require Import Flood_Properties.
Require Import Flood_Box.

Require Import add_message_to_all_properties.
Require Import extract_port_buffer_message_properties.
Require Import execute_flood_aux_properties.

Require Import List_Properties.


Definition buffer_reveals_input_in_trace_def (inp : inputs) : Prop :=
  forall buf port_buf trace i j p c m n,
  execute_flood_rec inp (Flood_Box_init n) = (trace, buf) ->
  nth_error buf i = Some port_buf ->
  nth_error port_buf j = Some (p, m, c) ->
  exists t, nth_error trace t = Some (Flood_Input p (m, c)).

Lemma buffer_reveals_input_in_trace:
  forall inp,
  buffer_reveals_input_in_trace_def inp.
Proof.
  apply rev_ind;
  unfold buffer_reveals_input_in_trace_def.
  - intros buf port_buf trace i j p c m n.
    intros H_exec H_index_port_buf H_index_mes.
    simpl in H_exec.
    inversion H_exec. subst. clear H_exec.
    assert (port_buf = [])
      as H_empty_port
      by (apply Flood_Box_init_buffers_empty with n i;
          assumption).
    rewrite H_empty_port in H_index_mes.
    destruct j;
    simpl in H_index_mes;
    discriminate.
  - intros a inp.
    intros H_ind.
    intros buf port_buf trace i j p c m n.
    intros H_exec H_index_port_buf H_index_mes.
    destruct a.
    + apply concat_inp_concats_trace_split in H_exec.
      destruct H_exec as [buf' H_exec].
      destruct H_exec as [trace_head H_exec].
      destruct H_exec as [trace_tail H_exec].
      destruct H_exec as [H_trace H_exec].
      destruct H_exec as [H_exec_inp H_exec_send].
      simpl in H_exec_send.
      destruct p0 in H_exec_send.
      inversion H_exec_send.
      assert (exists port_buf', port_buf = (n0, s, n1) :: port_buf')
        as H_port_buf
        by (apply add_message_to_all_reveals_older_messages with buf' buf i;
            auto).
      destruct H_port_buf as [port_buf' H_port_buf].
      rewrite H_port_buf in H_index_mes.
      destruct j.
      * simpl in H_index_mes.
        inversion H_index_mes.
        subst.
        exists (Datatypes.length trace_head).
        rewrite nth_error_app2.
        -- rewrite PeanoNat.Nat.sub_diag.
           simpl.
           reflexivity.
        -- apply PeanoNat.Nat.le_refl.
      * assert (exists t : nat, nth_error trace_head t = Some (Flood_Input p (m, c)))
          as H_trace_input.
        -- apply H_ind with buf' port_buf' i j n.
           ++ assumption.
           ++ eapply add_message_to_all_old_lookups;
              eauto.
              rewrite H1.
              rewrite <- H_port_buf.
              assumption.
           ++ simpl in H_index_mes.
              assumption.
        -- destruct H_trace_input as [t H_trace_input].
           exists t.
           rewrite H_trace.
           apply nth_succes_larger.
           assumption.
    + apply concat_inp_concats_trace_split in H_exec.
      destruct H_exec as [buf' H_exec].
      destruct H_exec as [trace_head H_exec].
      destruct H_exec as [trace_tail H_exec].
      destruct H_exec as [H_trace H_exec].
      destruct H_exec as [H_exec_inp H_exec_deliver].
      simpl in H_exec_deliver.
      destruct p0.
      destruct (extract_port_buffer buf' n1 n0 n1 s n2) eqn:extract.
      destruct o.
      * do 3 destruct p0.
        assert (n0 = n5 /\ n1 = n4 /\ s = s0 /\ n2 = n3)
          as H_eq
          by (eapply extract_port_buffer_success_same_output;
              eassumption).
        destruct H_eq as [H_eqi H_eq].
        destruct H_eq as [H_eqj H_eq].
        destruct H_eq as [H_eqm H_eqc].
        subst.
        inversion H_exec_deliver.
        subst. clear H_exec_deliver.
        assert (exists k' h' port_buf',
                  nth_error buf' k' = Some port_buf' /\
                  nth_error port_buf' h' = Some (p, m, c))
          as H_message_exists
          by (eapply extract_port_buffer_success_lookups_reveal_old;
              eassumption).
        destruct H_message_exists as [k' H_message_exists].
        destruct H_message_exists as [h' H_message_exists].
        destruct H_message_exists as [port_buf' H_message_exists].
        destruct H_message_exists as [H_mess_port_buf H_mess_exists].
        assert (exists t : nat, nth_error trace_head t = Some (Flood_Input p (m, c)))
          as H_trace_head_input
          by (eapply H_ind;
              eassumption).
        destruct H_trace_head_input as [t H_trace_head_input].
        exists t.
        rewrite concat_list_two.
        do 2 apply nth_succes_larger.
        assumption.
      * apply extract_port_buffer_none_action_same_buffer in extract.
        inversion H_exec_deliver.
        subst. clear H_exec_deliver.
        assert (exists t : nat, nth_error trace_head t = Some (Flood_Input p (m, c)))
          as H_trace_head_input
          by (apply H_ind with buf port_buf i j n;
              assumption).
        destruct H_trace_head_input as [t H_trace_head_input].
        exists t.
        apply nth_succes_larger.
        assumption.
Qed.
