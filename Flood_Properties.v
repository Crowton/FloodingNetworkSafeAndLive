
Require Import String.

Import List.
Import ListNotations.


Inductive Flood_Action : Set :=
| Flood_Input   : nat -> (string * nat) -> Flood_Action
| Flood_Leak    : nat -> (string * nat) -> Flood_Action
| Flood_Deliver : nat -> nat -> (string * nat) -> Flood_Action
| Flood_Output  : nat -> nat -> (string * nat) -> Flood_Action.

Definition Flood_Trace : Type := list Flood_Action.

Definition flood_safety (t: Flood_Trace) : Prop :=
  forall i j m c t2,
  nth_error t t2 = Some (Flood_Output i j (m, c)) ->
  exists t1, t1 < t2 /\ nth_error t t1 = Some (Flood_Input i (m, c)).

(* n = number of parties *)
Definition flood_liveness (t: Flood_Trace) (n: nat) : Prop :=
  forall i m c t1,
  nth_error t t1 = Some (Flood_Input i (m, c)) ->
  (forall j, j < n -> exists t2, t1 < t2 /\ nth_error t t2 = Some (Flood_Output i j (m, c))).
