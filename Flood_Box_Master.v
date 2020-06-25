
Require Import String.
Import List.
Import ListNotations.

Require Import Input_Properties.
Require Import Flood_Properties.
Require Import Flood_Box.

Require Import Flood_Box_Safety.
Require Import Flood_Box_Liveness.

Theorem Flood_Box_Safety_and_Liveness:
  forall inp n trace,
  user_contract inp ->
  execute_flood inp n = trace ->
    flood_safety trace /\
    (input_liveness inp n -> flood_liveness trace n).
Proof.
  intros inp n trace.
  intros H_contract H_exec.
  split.
  - eapply Flood_Box_Safety;
    eassumption.
  - intros H_inp_live.
    eapply Flood_Box_Liveness;
    eassumption.
Qed.

