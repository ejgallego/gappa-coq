Require Import Gappa_tactic.

Goal forall x,
  (x <= 4 /\ 3 <= x -> x - 2 <= 2)%R.
intros.
gappa.
Qed.
