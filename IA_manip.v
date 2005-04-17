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

Theorem absolute_transitivity :
 forall a b c : R, forall zi : FF,
 IintF zi ((a - c) + (c - b)) ->
 true = true ->
 IintF zi (a - b).
intros a b c zi Hz _.
replace (a - b)%R with ((a - c) + (c - b))%R.
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

Definition sub_decomposition_rounded_left :=
 absolute_transitivity.

Theorem mul_decomposition_rounded_right :
 forall a b c : R, forall zi : FF,
 IintF zi (a * (b - c) + a * c) ->
 true = true ->
 IintF zi (a * b).
intros a b c zi Hz _.
replace (a * b)%R with (a * (b - c) + a * c)%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_factor_left :
 forall a b c : R, forall zi : FF,
 IintF zi (a * (b - c)) ->
 true = true ->
 IintF zi (a * b - a * c).
intros a b c zi Hz _.
replace (a * b - a * c)%R with (a * (b - c))%R.
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
