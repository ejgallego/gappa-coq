Require Import Gappa_tactic.

Open Scope R_scope.

Goal forall fma x' x_ éà,
  fma = 1 ->
  x' = 2 ->
  x_ = 3 ->
  éà = 4 ->
  10 <= fma + x' + x_ + éà <= 10.
Proof.
gappa.
Qed.
