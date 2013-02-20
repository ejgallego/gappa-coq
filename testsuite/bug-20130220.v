Require Import Gappa_tactic.

Lemma truc :
  forall b, (Rabs b <= 1 -> Rabs b <= 2)%R.
Proof.
gappa.
Qed.

