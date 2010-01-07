Require Import Reals.
Require Import Gappa_tactic.

Definition rnd := gappa_rounding (rounding_float roundNE 53 1074).

Goal
  forall a_ b_ a b : R,
  a = rnd a_ ->
  b = rnd b_ ->
  (Rabs (rnd (a + b) - (a + b)) <= powerRZ 2 (-50) * Rabs (a + b))%R.
Proof.
unfold rnd.
gappa.
Qed.
