Require Import Reals.
Require Import Fcore.
Require Import Gappa_tactic.
Open Scope R_scope.

Definition format :=
  generic_format radix2 (FLT_exp (-1074) 53).
Notation rnd :=
  (round radix2 (FLT_exp (-1074) 53) rndZR).

Goal
  forall a b : R,
  format a -> format b ->
  52 / 16 <= a <= 53 / 16 ->
  22 / 16 <= b <= 30 / 16 ->
  format (a - b).
Proof.
  intros a b Ha Hb Ia Ib.
  change (a - b = rnd (a - b)).
  revert Ia Ib.
  replace a with (rnd a).
  replace b with (rnd b).
  gappa.
Qed.
