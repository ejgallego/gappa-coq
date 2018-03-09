Require Import Reals Gappa_tactic.

Goal forall x, (IZR x - IZR x = 0)%R.
Proof.
gappa.
Qed.
