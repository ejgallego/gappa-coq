Require Import IA_real.
Require Import IA_comput.

Section IA_manip.

Theorem neg_sub :
 forall a b : R, forall zi : FF,
 IintF zi (-(b - a)) ->
 true = true ->
 IintF zi (a - b).
intros a b zi Hz _.
replace (a - b)%R with (-(b - a))%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition :
 forall a b c d : R, forall zi : FF,
 IintF zi ((a - c) + (b - d)) ->
 true = true ->
 IintF zi ((a + b) - (c + d)).
intros a b c d zi Hz _.
replace ((a + b) - (c + d))%R with ((a - c) + (b - d))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition :
 forall a b c d : R, forall zi : FF,
 IintF zi ((a - c) - (b - d)) ->
 true = true ->
 IintF zi ((a - b) - (c - d)).
intros a b c d zi Hz _.
replace ((a - b) - (c - d))%R with ((a - c) - (b - d))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_simple :
 forall a b c d : R, forall zi : FF,
 IintF zi (a * (b - d) + d * (a - c)) ->
 true = true ->
 IintF zi (a * b - c * d).
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (a * (b - d) + d * (a - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_full_left :
 forall a b c d : R, forall zi : FF,
 IintF zi (a * (b - d) + b * (a - c) - (a - c) * (b - d)) ->
 true = true ->
 IintF zi (a * b - c * d).
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (a * (b - d) + b * (a - c) - (a - c) * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_full_right :
 forall a b c d : R, forall zi : FF,
 IintF zi (c * (b - d) + d * (a - c) + (a - c) * (b - d)) ->
 true = true ->
 IintF zi (a * b - c * d).
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (c * (b - d) + d * (a - c) + (a - c) * (b - d))%R.
exact Hz.
ring.
Qed.

End IA_manip.
