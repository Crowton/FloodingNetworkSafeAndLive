
Require Import String.
Import List.
Import ListNotations.

Require Import Input_Properties.
Require Import Flood_Properties.
Require Import Flood_Box.

Require Import List_Properties.

Require Import flood_safety_properties.

Require Import execute_flood_aux_properties.
Require Import extract_port_buffer_message_properties.

Require Import buffer_reveals_input_in_trace.



Definition Flood_Box_Safety_def (inp: inputs) : Prop :=
  forall n trace,
  user_contract inp ->
  execute_flood inp n = trace ->
  flood_safety trace.

Theorem Flood_Box_Safety:
  forall inp,
  Flood_Box_Safety_def inp.
Proof.
  apply rev_ind;
  unfold Flood_Box_Safety_def.
  - intros n trace.
    intros H_contract H_exec.
    unfold execute_flood in H_exec.
    simpl in H_exec.
    subst.
    unfold flood_safety.
    intros i j m c t2 H_nth.
    destruct t2;
    simpl in H_nth;
    discriminate.
  - intros action inp.
    intros H_ind.
    intros n trace.
    intros H_contract H_exec.
    unfold execute_flood in H_exec.
    set (exec := execute_flood_rec (inp ++ [action]) (Flood_Box_init n)).
    destruct (execute_flood_rec (inp ++ [action]) (Flood_Box_init n)) eqn:executer.
    apply concat_inp_concats_trace_split in executer.
    destruct executer as [buf' executer].
    destruct executer as [trace_head executer].
    destruct executer as [trace_tail executer].
    destruct executer as [trace_concat executer].
    destruct executer as [exec_inp exec_action].
    simpl in H_exec.
    rewrite <- H_exec.
    rewrite trace_concat.
    assert (flood_safety trace_head).
    + apply H_ind with n.
      * apply user_contract_smaller_append with action.
        assumption.
      * unfold execute_flood.
        rewrite exec_inp.
        simpl.
        reflexivity.
    + destruct action.
      * simpl in exec_action.
        destruct p.
        inversion exec_action.
        rewrite concat_list_two.
        apply flood_safety_append_leak.
        apply flood_safety_append_input.
        assumption.
      * simpl in exec_action.
        destruct p.
        destruct (extract_port_buffer buf' n1 n0 n1 s n2) eqn:extract.
        destruct o.
        -- do 3 destruct p.
           inversion exec_action.
           subst. clear exec_action.
           assert (n0 = n5 /\ n1 = n4 /\ s = s0 /\ n2 = n3)
             as H_eq
             by (eapply extract_port_buffer_success_same_output;
                 eassumption).
           destruct H_eq as [H_eqi H_eq].
           destruct H_eq as [H_eqj H_eq].
           destruct H_eq as [H_eqm H_eqc].
           subst.
           assert (exists k h port_buf,
                    (nth_error buf' k = Some port_buf /\
                     nth_error port_buf h = Some (n5, s0, n3)))
             as H_mess_must_exists
             by (eapply extract_port_buffer_success_reveal_message;
                 eassumption).
           destruct H_mess_must_exists as [k H_mess_must_exists].
           destruct H_mess_must_exists as [h H_mess_must_exists].
           destruct H_mess_must_exists as [port_buf H_mess_must_exists].
           destruct H_mess_must_exists as [H_mess_port_buf H_mess_exists].
           assert (exists t, nth_error trace_head t = Some (Flood_Input n5 (s0, n3)))
             as H_trace_head_input
             by (eapply buffer_reveals_input_in_trace;
                 eassumption).
           destruct H_trace_head_input as [t H_trace_head_input].
           rewrite concat_list_two.
           apply flood_safety_append_output with t.
           ++ apply flood_safety_append_deliver.
              assumption.
           ++ apply nth_succes_larger.
              assumption.
        -- inversion exec_action.
           apply flood_safety_append_deliver.
           assumption.
Qed.
