Require Import Reals.
Require Import Gappa_tactic.

Goal
  forall a1 a2 b1 b2 : R,
  (Rabs (a1 - a2) <= 1/16 * Rabs a2)%R ->
  (Rabs (b1 - b2) <= 1/16 * Rabs b2)%R ->
  (Rabs (a1 * b1 - a2 * b2) <= 33/256 * Rabs (a2 * b2))%R.
Proof.
gappa.
Qed.
