From Coq Require Import Reals.
From Flocq Require Import Core.
From Gappa Require Import Gappa_tactic.
Open Scope R_scope.

Goal
  forall x y : R,
  3/4 <= x <= 3 ->
  0 <= sqrt x <= 1775 * powerRZ 2 (-10).
Proof.
  gappa.
Qed.

Definition rnd := rounding_float rndZR 53 (-1074).

Goal
  forall a_ b_ a b : R,
  a = rnd a_ ->
  b = rnd b_ ->
  52 / 16 <= a <= 53 / 16 ->
  22 / 16 <= b <= 30 / 16 ->
  0 <= rnd (a - b) - (a - b) <= 0.
Proof.
  unfold rnd ; gappa.
Qed.
