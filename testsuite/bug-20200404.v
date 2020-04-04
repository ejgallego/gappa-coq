Require Import Reals Gappa_tactic.
Open Scope R_scope.

Goal -10 <= 12 * powerRZ 2 (-3) <= 10.
Proof. gappa. Qed.

Goal -10 <= 150 * powerRZ 10 (-2) <= 10.
Proof. gappa. Qed.

Goal -10 <= 24 * powerRZ 2 (-3) <= 10.
Proof. gappa. Qed.

Goal -10 <= 0 * powerRZ 10 (-3) <= 10.
Proof. gappa. Qed.

Goal -10 <= -300 * powerRZ 10 (-2) <= 10.
Proof. gappa. Qed.

Goal -10 <= -12 * powerRZ 2 (-3) <= 10.
Proof. gappa. Qed.

Goal -10 <= -150 * powerRZ 10 (-2) <= 10.
Proof. gappa. Qed.
