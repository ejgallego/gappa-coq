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

Theorem mul_decomposition_half_left :
 forall a b c d : R, forall zi : FF,
 IintF zi (a * (b - d) + (a - c) * d) ->
 true = true ->
 IintF zi (a * b - c * d).
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * d)%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_half_right :
 forall a b c d : R, forall zi : FF,
 IintF zi ((a - c) * b + c * (b - d)) ->
 true = true ->
 IintF zi (a * b - c * d).
intros a b c d zi Hz _.
replace (a * b - c * d)%R with ((a - c) * b + c * (b - d))%R.
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

Theorem relative_to_absolute :
 forall a b : R, forall bi zi : FF,
 IintF bi b -> IintF zi (a / b * b) ->
 not_zero bi = true ->
 IintF zi a.
intros a b bi zi Hb Hz H.
generalize (not_zero_correct _ _ Hb H). clear Hb H. intro H.
replace a with (a / b * b)%R.
exact Hz.
field.
exact H.
Qed.

Theorem relative_transitivity :
 forall a b c : R, forall bi ci zi : FF,
 IintF bi b -> IintF ci c ->
 IintF zi ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b)) ->
 not_zero bi && not_zero ci = true ->
 IintF zi ((a - b) / b).
intros a b c bi ci zi Hb Hc Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (not_zero_correct _ _ Hb H1). clear Hb H1. intro Hb.
generalize (not_zero_correct _ _ Hc H2). clear Hc H2. intro Hc.
replace ((a - b) / b)%R with ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b))%R.
exact Hz.
field.
auto with real.
Qed.

End IA_manip.
