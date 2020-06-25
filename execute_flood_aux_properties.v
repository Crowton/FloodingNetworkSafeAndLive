
Require Import String.
Import List.
Import ListNotations.

Require Import List_Properties.

Require Import Input_Properties.
Require Import Flood_Properties.
Require Import Flood_Box.

Require Import add_message_to_all_properties.
Require Import extract_port_buffer_message_properties.


Lemma resume_run_concats_trace:
  forall inp inp' buf buf' buf'' trace trace',
  execute_flood_rec inp buf = (trace, buf') ->
  execute_flood_rec inp' buf' = (trace', buf'') ->
  execute_flood_rec (inp ++ inp') buf = (trace ++ trace', buf'').
Proof.
  intros inp.
  induction inp;
  intros inp' buf buf' buf'' trace trace';
  intros H_first_run H_second_run.
  - simpl in * |- *.
    inversion H_first_run.
    subst. simpl.
    assumption.
  - destruct a;
    simpl.
    + destruct p.
      simpl in H_first_run.
      destruct (execute_flood_rec inp (add_message_to_all buf n s n0)) eqn:first_run_rem in H_first_run.
      inversion H_first_run. subst. clear H_first_run.
      rewrite IHinp with inp' (add_message_to_all buf n s n0) buf' buf'' f trace';
      try assumption.
      simpl. reflexivity.
    + simpl in H_first_run.
      destruct p.
      destruct (extract_port_buffer buf n0 n n0 s n1).
      destruct o;
      try (do 3 destruct p);
      destruct (execute_flood_rec inp i) eqn:first_run_rem in H_first_run;
      inversion H_first_run; subst; clear H_first_run;
      rewrite IHinp with inp' i buf' buf'' f trace';
      try assumption;
      simpl; reflexivity.
Qed.


Lemma concat_inp_concats_trace_split:
  forall inp inp' buf buf'' trace,
  execute_flood_rec (inp ++ inp') buf = (trace, buf'') ->
    exists buf' trace_head trace_tail,
      trace = trace_head ++ trace_tail /\
      execute_flood_rec inp buf = (trace_head, buf') /\
      execute_flood_rec inp' buf' = (trace_tail, buf'').
Proof.
  intros inp.
  induction inp;
  intros inp' buf buf'' trace;
  intros H_exec.
  - simpl in H_exec.
    exists buf, [], trace.
    repeat split. (* splits /\ and also fixes goal 1 and 2 *)
    assumption.
  - simpl in H_exec.
    destruct a.
    + destruct p.
      destruct (execute_flood_rec (inp ++ inp') (add_message_to_all buf n s n0)) eqn:rem.
      inversion H_exec.
      subst. clear H_exec.
      assert (exists (buf' : In_transit_buffer) (trace_head trace_tail : Flood_Trace),
          f = trace_head ++ trace_tail /\
          execute_flood_rec inp (add_message_to_all buf n s n0) = (trace_head, buf') /\
          execute_flood_rec inp' buf' = (trace_tail, buf'')).
      * apply IHinp.
        assumption.
      * do 4 destruct H.
        destruct H0.
        exists x.
        exists (Flood_Input n (s, n0) :: Flood_Leak n (s, n0) :: x0).
        exists x1.
        repeat split.
        -- simpl.
           rewrite H.
           reflexivity.
        -- simpl.
           rewrite H0.
           reflexivity.
        -- assumption.
    + destruct p.
      destruct (extract_port_buffer buf n0 n n0 s n1) eqn:buf_rem in H_exec.
      destruct o.
      * do 3 destruct p.
        destruct (execute_flood_rec (inp ++ inp') i) eqn:rem.
        assert (exists (buf' : In_transit_buffer) (trace_head trace_tail : Flood_Trace),
                  f = trace_head ++ trace_tail /\
                  execute_flood_rec inp i = (trace_head, buf') /\
                  execute_flood_rec inp' buf' = (trace_tail, i0)).
        -- apply IHinp.
           assumption.
        -- do 4 destruct H.
           destruct H0.
           exists x.
           exists (Flood_Deliver n4 n3 (s0, n2) :: Flood_Output n4 n3 (s0, n2) :: x0).
           exists x1.
           repeat split.
           ++ simpl.
              rewrite H in H_exec.
              inversion H_exec.
              reflexivity.
           ++ simpl.
              rewrite buf_rem.
              rewrite H0.
              reflexivity.
           ++ inversion H_exec.
              subst.
              assumption.
      * destruct (execute_flood_rec (inp ++ inp') i) eqn:rem.
        assert (exists (buf' : In_transit_buffer) (trace_head trace_tail : Flood_Trace),
                  f = trace_head ++ trace_tail /\
                  execute_flood_rec inp i = (trace_head, buf') /\
                  execute_flood_rec inp' buf' = (trace_tail, i0)).
        -- apply IHinp.
           assumption.
        -- do 4 destruct H.
           destruct H0.
           exists x.
           exists (Flood_Deliver n n0 (s, n1) :: x0).
           exists x1.
           repeat split.
           ++ simpl.
              rewrite H in H_exec.
              inversion H_exec.
              reflexivity.
           ++ simpl.
              rewrite buf_rem.
              rewrite H0.
              reflexivity.
           ++ inversion H_exec.
              subst.
              assumption.
Qed.

Lemma input_in_trace_implies_send_in_inp:
  forall inp trace buf buf' t1 i m c,
  execute_flood_rec inp buf = (trace, buf') ->
  nth_error trace t1 = Some (Flood_Input i (m, c)) ->
  exists t1', nth_error inp t1' = Some (Send i (m, c)).
Proof.
  intros inp.
  induction inp;
  intros trace buf buf' t1 i m c;
  intros H_exec H_nth_input;
  unfold execute_flood in H_exec;
  simpl in H_exec.
  - inversion H_exec.
    subst.
    destruct t1;
    simpl in H_nth_input;
    discriminate.
  - destruct a.
    + destruct p.
      destruct (execute_flood_rec inp (add_message_to_all buf n s n0)) eqn:exec_tail.
      inversion H_exec.
      subst. clear H_exec.
      destruct t1;
      simpl in H_nth_input.
      * inversion H_nth_input.
        subst.
        exists 0.
        simpl.
        reflexivity.
      * destruct t1;
        simpl in H_nth_input.
        -- inversion H_nth_input.
        -- assert (exists t1', nth_error inp t1' = Some (Send i (m, c)))
             as H_send_in_tail
             by (eapply IHinp;
                 eassumption).
           destruct H_send_in_tail as [t1' H_send_in_tail].
           exists (S t1').
           simpl.
           assumption.
    + destruct p.
      destruct (extract_port_buffer buf n0 n n0 s n1).  (* This has to be shortable *)
      destruct o.
      * do 3 destruct p.
        destruct (execute_flood_rec inp i0) eqn:exec_tail.
        inversion H_exec.
        subst. clear H_exec.
        destruct t1;
        simpl in H_nth_input.
        -- inversion H_nth_input.
        -- destruct t1;
           simpl in H_nth_input.
           ++ inversion H_nth_input.
           ++ assert (exists t1', nth_error inp t1' = Some (Send i (m, c)))
                as H_send_in_tail
                by (eapply IHinp;
                    eassumption).
              destruct H_send_in_tail as [t1' H_send_in_tail].
              exists (S t1').
              simpl.
              assumption.
      * destruct (execute_flood_rec inp i0) eqn:exec_tail.
        inversion H_exec.
        subst. clear H_exec.
        destruct t1;
        simpl in H_nth_input.
        -- inversion H_nth_input.
        -- assert (exists t1', nth_error inp t1' = Some (Send i (m, c)))
             as H_send_in_tail
             by (eapply IHinp;
                 eassumption).
           destruct H_send_in_tail as [t1' H_send_in_tail].
           exists (S t1').
           simpl.
           assumption.
Qed.

Lemma input_in_trace_implies_late_send_in_inp:
  forall inp trace buf buf' t1 i m c,
  execute_flood_rec inp buf = (trace, buf') ->
  nth_error trace t1 = Some (Flood_Input i (m, c)) ->
  exists t1', nth_error inp t1' = Some (Send i (m, c))
    /\ no_late_specific_send inp t1' i m c.
Proof.
  intros inp trace buf buf' t1 i m c.
  intros H_exec H_nth_input.
  assert (exists t1', nth_error inp t1' = Some (Send i (m, c)))
    as H_send_in_inp
    by (eapply input_in_trace_implies_send_in_inp;
        eassumption).
  destruct H_send_in_inp as [t1' H_send_in_inp].
  assert ((exists t, nth_error inp t = Some (Send i (m, c))
            /\ no_late_specific_send inp t i m c)
            \/ (forall t, nth_error inp t <> Some (Send i (m, c))))
    as H_send_late_or_not
    by (apply send_late_or_not_in_inp).
  destruct H_send_late_or_not as [H_send_late | H_no_send].
  - assumption.
  - specialize (H_no_send t1').
    contradiction.
Qed.

Lemma execute_flood_aux_rec_deliver_no_input_trace:
  forall i j m c trace buf buf' i' m' c',
  execute_flood_rec [Deliver i j (m, c)] buf = (trace, buf') ->
  ~ In (Flood_Input i' (m', c')) trace.
Proof.
  intros i j m c trace buf buf' i' m' c'.
  unfold not.
  intros H_exec H_in.
  simpl in H_exec.
  destruct (extract_port_buffer buf j i j m c).
  destruct o.
  - do 3 destruct p.
    inversion H_exec.
    subst. clear H_exec.
    inversion H_in.
    + discriminate.
    + inversion H.
      * discriminate.
      * inversion H0.
  - inversion H_exec.
    subst. clear H_exec.
    inversion H_in.
    + discriminate.
    + inversion H.
Qed.

Lemma send_in_inp_head_implies_send_in_trace_head:
  forall inp action t t' i m c trace_head trace_tail buf' buf'',
  nth_error inp t = Some (Send i (m, c)) ->
  no_late_specific_send (inp ++ [action]) t i m c ->
  execute_flood_rec [action] buf' = (trace_tail, buf'') ->
  nth_error (trace_head ++ trace_tail) t' = Some (Flood_Input i (m, c)) ->
  nth_error trace_head t' = Some (Flood_Input i (m, c)).
Proof.
  intros inp action t t' i m c trace_head trace_tail buf' buf''.
  intros H_inp_send H_inp_no_late_send H_exec_action H_trace_input.
  apply nth_error_concat_not_in_tail_implies_head with trace_tail.
  - assumption.
  - unfold not.
    intros H_in.
    destruct action.
    + simpl in H_exec_action.
      destruct p.
      inversion H_exec_action.
      subst. clear H_exec_action.
      inversion H_in.
      * inversion H.
        subst. clear H.
        unfold no_late_specific_send in H_inp_no_late_send.
        specialize (H_inp_no_late_send (Datatypes.length inp) i m c).
        apply H_inp_no_late_send.
        -- apply nth_error_Some.
           unfold not.
           intros H_is_none.
           rewrite H_is_none in H_inp_send.
           discriminate.
        -- rewrite nth_error_app2.
           ++ rewrite PeanoNat.Nat.sub_diag.
              simpl.
              reflexivity.
           ++ apply PeanoNat.Nat.le_refl.
        -- reflexivity.
      * inversion H;
        inversion H0.
    + simpl in H_exec_action.
      destruct p.
      destruct (extract_port_buffer buf' n0 n n0 s n1).
      destruct o.
      * do 3 destruct p.
        inversion H_exec_action.
        subst. clear H_exec_action.
        inversion H_in;
        inversion H;
        inversion H0.
      * inversion H_exec_action.
        subst. clear H_exec_action.
        inversion H_in;
        inversion H.
Qed.

Lemma length_of_flood_init_is_param:
  forall n,
  Datatypes.length (Flood_Box_init n) = n.
Proof.
  intros n.
  induction n;
  simpl.
  - reflexivity.
  - rewrite IHn.
    reflexivity.
Qed.

Lemma execute_inp_preserves_buffer_length:
  forall inp buf buf' trace,
  execute_flood_rec inp buf = (trace, buf') ->
  Datatypes.length buf = Datatypes.length buf'.
Proof.
  intros inp.
  induction inp;
  intros buf buf' trace;
  intros H_exec;
  simpl in H_exec.
  - inversion H_exec.
    reflexivity.
  - destruct a.
    + destruct p.
      destruct (execute_flood_rec inp (add_message_to_all buf n s n0)) eqn:exec.
      inversion H_exec.
      subst. clear H_exec.
      rewrite <- IHinp with (add_message_to_all buf n s n0) buf' f.
      * apply add_message_to_all_preserves_length.
      * assumption.
    + destruct p.
      destruct (extract_port_buffer buf n0 n n0 s n1) eqn:extract.
      destruct o;
      try do 3 destruct p;
      destruct (execute_flood_rec inp i) eqn:exec;
      inversion H_exec;
      subst; clear H_exec;
      rewrite <- IHinp with i buf' f;
      try (eapply extract_port_buffer_preserves_length;
           eassumption);
      assumption.
Qed.
