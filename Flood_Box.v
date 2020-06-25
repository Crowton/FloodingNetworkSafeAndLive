
Require Import String.

Import List.
Import ListNotations.

Set Implicit Arguments.

Require Import Flood_Properties.
Require Import Input_Properties.



Definition In_transit_port_buffer : Type := list (nat * string * nat).
Definition In_transit_buffer : Type := list In_transit_port_buffer.

Definition Flood_Box_init (n: nat) : In_transit_buffer :=
  let fix rec (n: nat) : In_transit_buffer :=
    match n with
    | 0 => []
    | S n' => [] :: (rec n')
    end
  in
  rec n.

Lemma Flood_Box_init_buffers_empty:
  forall n i port_buf,
  nth_error (Flood_Box_init n) i = Some port_buf ->
  port_buf = [].
Proof.
  intro n.
  induction n;
  intros i port_buf H_nth.
  - destruct i;
    simpl in H_nth;
    discriminate.
  - destruct i.
    + simpl in H_nth.
      inversion H_nth.
      reflexivity.
    + simpl in H_nth.
      apply IHn with i.
      assumption.
Qed.



Fixpoint add_message_to_all (inTransit : In_transit_buffer) i m c : In_transit_buffer :=
  match inTransit with
  | [] => []
  | inTransitSingle :: inTransitPart =>
     ((i, m, c) :: inTransitSingle) :: (add_message_to_all inTransitPart i m c)
  end.

Definition triple_and (a b c : bool) : bool :=
  match (a, b, c) with
  | (true, true, true) => true
  | _ => false
  end.

Fixpoint extract_message
  (inTransitSinglePart : In_transit_port_buffer)
  i j m c
  : (In_transit_port_buffer * option (nat * nat * string * nat))
  :=
  match inTransitSinglePart with
  | [] => ([], None)
  | (i', m', c') :: inTransitSinglePart' =>
       if triple_and (Nat.eqb i i') (String.eqb m m') (Nat.eqb c c') then
           (inTransitSinglePart', Some (j, i, m, c))
       else
           match extract_message inTransitSinglePart' i j m c with
           | (inTransitSinglePartFixed, ret) =>
                 ((i', m', c') :: inTransitSinglePartFixed, ret)
           end
  end.

Fixpoint extract_port_buffer
  (inTransitPart : In_transit_buffer)
  (portPart : nat)
  i j m c
  : (In_transit_buffer * option (nat * nat * string * nat))
  := match (inTransitPart, portPart) with
     | ([], _) => ([], None)  (* Fails to find buffer j *)
     | (inTransitSingle :: inTransitPart', 0) =>
            match extract_message inTransitSingle i j m c with
            | (inTransitSingleFixed, ret) =>
                  (inTransitSingleFixed :: inTransitPart', ret)
            end
     | (inTransitSingle :: inTransitPart', S portPart') =>
          match extract_port_buffer inTransitPart' portPart' i j m c with
          | (inTransitPartFixed, ret) =>
                (inTransitSingle :: inTransitPartFixed, ret)
          end
     end.

Definition Flood_Box
  (inTransit : In_transit_buffer)
  (inp : input)
  (* Optional output j i m c says to output (i, m, c) om port j *)
  : (In_transit_buffer * option (nat * nat * string * nat))
  := match inp with
     | Send i (m, c) =>
        (add_message_to_all inTransit i m c, None)
     | Deliver i j (m, c) =>
        extract_port_buffer inTransit j i j m c
     end.

Fixpoint execute_flood_rec (inp: inputs) (inTransit: In_transit_buffer) : (Flood_Trace * In_transit_buffer) :=
  match inp with
  | [] => ([], inTransit)
  | Send i (m, c) :: inp' =>
      match Flood_Box inTransit (Send i (m, c)) with
      | (inTransit', _) =>
          let (trace', inTransitFinal) := execute_flood_rec inp' inTransit' in
          (Flood_Input i (m, c) :: Flood_Leak i (m, c) :: trace', inTransitFinal)
      end
  | Deliver i j (m, c) :: inp' =>
      match Flood_Box inTransit (Deliver i j (m, c)) with
      | (inTransit', None) =>
          let (trace', inTransitFinal) := execute_flood_rec inp' inTransit' in
          (Flood_Deliver i j (m, c) :: trace', inTransitFinal)
      | (inTransit', Some (j, i, m, c)) =>
          let (trace', inTransitFinal) := execute_flood_rec inp' inTransit' in
          (Flood_Deliver i j (m, c) :: Flood_Output i j (m, c) :: trace', inTransitFinal)
      end
  end.

Definition execute_flood (inp: inputs) (n: nat) : Flood_Trace :=
  fst (execute_flood_rec inp (Flood_Box_init n)).
