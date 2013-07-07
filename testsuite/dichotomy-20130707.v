Require Import Gappa_tactic.

Goal forall x,
  (1 <= x <= 5 -> 3 <= x <= 4 \/ 4 <= x <= 6 \/ 1 <= x + 1 <= 4)%R.
Proof.
gappa.
Qed.
