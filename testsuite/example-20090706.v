Require Import Reals.
Require Import Gappa_tactic.
Open Scope R_scope.

Definition floor := (gappa_rounding (rounding_fixed roundDN 0)).

Goal forall x y,
  floor x = floor y ->
  2 <= sqrt (4 + Rsqr (x - y)) <= 9/4.
Proof.
unfold floor, Rsqr.
gappa.
Qed.
