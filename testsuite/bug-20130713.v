Require Import Gappa_tactic.

Goal forall x, (1/4 <= x <= 3/4 -> 0 <= x /\ not (1 <= x))%R.
gappa.
Qed.
