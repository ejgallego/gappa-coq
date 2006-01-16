Require Import Reals.
Require Import Gappa_common.

Section Gappa_rewriting.

Theorem add_decomposition_rounded_left :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + (c + b)) zi ->
 true = true ->
 BND (a + b) zi.
intros a b c zi Hz _.
replace (a + b)%R with ((a - c) + (c + b))%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition_rounded_right :
 forall a b c : R, forall zi : FF,
 BND ((a + c) + (b - c)) zi ->
 true = true ->
 BND (a + b) zi.
intros a b c zi Hz _.
replace (a + b)%R with ((a + c) + (b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_rounded_left :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + (c - b)) zi ->
 true = true ->
 BND (a - b) zi.
intros a b c zi Hz _.
replace (a - b)%R with ((a - c) + (c - b))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_rounded_right :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + -(b - c)) zi ->
 true = true ->
 BND (a - b) zi.
intros a b c zi Hz _.
replace (a - b)%R with ((a - c) + -(b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_rounded_left :
 forall a b c : R, forall zi : FF,
 BND ((a - c) * b + c * b) zi ->
 true = true ->
 BND (a * b) zi.
intros a b c zi Hz _.
replace (a * b)%R with ((a - c) * b + c * b)%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_rounded_right :
 forall a b c : R, forall zi : FF,
 BND (a * (b - c) + a * c) zi ->
 true = true ->
 BND (a * b) zi.
intros a b c zi Hz _.
replace (a * b)%R with (a * (b - c) + a * c)%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) + (b - d)) zi ->
 true = true ->
 BND ((a + b) - (c + d)) zi.
intros a b c d zi Hz _.
replace ((a + b) - (c + d))%R with ((a - c) + (b - d))%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition_left :
 forall a b c : R, forall zi : FF,
 BND (b - c) zi ->
 true = true ->
 BND ((a + b) - (a + c)) zi.
intros a b c zi Hz _.
replace ((a + b) - (a + c))%R with (b - c)%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition_right :
 forall a b c : R, forall zi : FF,
 BND (a - c) zi ->
 true = true ->
 BND ((a + b) - (c + b)) zi.
intros a b c zi Hz _.
replace ((a + b) - (c + b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) + -(b - d)) zi ->
 true = true ->
 BND ((a - b) - (c - d)) zi.
intros a b c d zi Hz _.
replace ((a - b) - (c - d))%R with ((a - c) + -(b - d))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_left :
 forall a b c : R, forall zi : FF,
 BND (-(b - c)) zi ->
 true = true ->
 BND ((a - b) - (a - c)) zi.
intros a b c zi Hz _.
replace ((a - b) - (a - c))%R with (-(b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_right :
 forall a b c : R, forall zi : FF,
 BND (a - c) zi ->
 true = true ->
 BND ((a - b) - (c - b)) zi.
intros a b c zi Hz _.
replace ((a - b) - (c - b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_factor_left :
 forall a b c : R, forall zi : FF,
 BND (a * (b - c)) zi ->
 true = true ->
 BND (a * b - a * c) zi.
intros a b c zi Hz _.
replace (a * b - a * c)%R with (a * (b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_factor_right :
 forall a b c : R, forall zi : FF,
 BND ((a - c) * b) zi ->
 true = true ->
 BND (a * b - c * b) zi.
intros a b c zi Hz _.
replace (a * b - c * b)%R with ((a - c) * b)%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_half_left :
 forall a b c d : R, forall zi : FF,
 BND (a * (b - d) + (a - c) * d) zi ->
 true = true ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * d)%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_half_right :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) * b + c * (b - d)) zi ->
 true = true ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz _.
replace (a * b - c * d)%R with ((a - c) * b + c * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_full_left :
 forall a b c d : R, forall zi : FF,
 BND (a * (b - d) + (a - c) * b + -((a - c) * (b - d))) zi ->
 true = true ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * b + -((a - c) * (b - d)))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_full_right :
 forall a b c d : R, forall zi : FF,
 BND (c * (b - d) + d * (a - c) + (a - c) * (b - d)) zi ->
 true = true ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz _.
replace (a * b - c * d)%R with (c * (b - d) + d * (a - c) + (a - c) * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem relative_to_absolute :
 forall a b : R, forall bi zi : FF,
 ABS b bi -> BND (a / b * b) zi ->
 abs_not_zero bi = true ->
 BND a zi.
intros a b bi zi Hb Hz H.
generalize (abs_not_zero_correct _ _ Hb H). clear Hb H. intro H.
replace a with (a / b * b)%R.
exact Hz.
field.
exact H.
Qed.

Theorem relative_transitivity :
 forall a b c : R, forall bi ci zi : FF,
 ABS b bi -> ABS c ci ->
 BND ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b)) zi ->
 abs_not_zero bi && abs_not_zero ci = true ->
 BND ((a - b) / b) zi.
intros a b c bi ci zi Hb Hc Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Hb H1). clear Hb H1. intro Hb.
generalize (abs_not_zero_correct _ _ Hc H2). clear Hc H2. intro Hc.
replace ((a - b) / b)%R with ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b))%R.
exact Hz.
field.
auto with real.
Qed.

Theorem mul_rel_decomposition :
 forall a b c d : R, forall ci di zi : FF,
 ABS c ci -> ABS d di ->
 BND ((a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d)) zi ->
 abs_not_zero ci && abs_not_zero di = true ->
 BND ((a * b - c * d) / (c * d)) zi.
intros a b c d ci di zi Hc Hd Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Hc H1). clear Hc H1. intro Hc.
generalize (abs_not_zero_correct _ _ Hd H2). clear Hd H2. intro Hd.
replace ((a * b - c * d) / (c * d))%R with ((a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d))%R.
exact Hz.
field.
repeat ( apply Rmult_integral_contrapositive ; split ) ; assumption.
Qed.

Theorem mul_rel_decomposition_left :
 forall a b c : R, forall ai ci zi : FF,
 ABS a ai -> ABS c ci ->
 BND ((b - c) / c) zi ->
 abs_not_zero ai && abs_not_zero ci = true ->
 BND ((a * b - a * c) / (a * c)) zi.
intros a b c ai ci zi Ha Hc Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Ha H1). clear Ha H1. intro Ha.
generalize (abs_not_zero_correct _ _ Hc H2). clear Hc H2. intro Hc.
replace ((a * b - a * c) / (a * c))%R with ((b - c) / c)%R.
exact Hz.
field.
repeat ( apply Rmult_integral_contrapositive ; split ) ; assumption.
Qed.

Theorem mul_rel_decomposition_right :
 forall a b c : R, forall bi ci zi : FF,
 ABS b bi -> ABS c ci ->
 BND ((a - c) / c) zi ->
 abs_not_zero bi && abs_not_zero ci = true ->
 BND ((a * b - c * b) / (c * b)) zi.
intros a b c bi ci zi Hb Hc Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Hb H1). clear Hb H1. intro Hb.
generalize (abs_not_zero_correct _ _ Hc H2). clear Hc H2. intro Hc.
replace ((a * b - c * b) / (c * b))%R with ((a - c) / c)%R.
exact Hz.
field.
repeat ( apply Rmult_integral_contrapositive ; split ) ; assumption.
Qed.

Theorem abs_mul_xx :
 forall a b : R, forall zi : FF,
 BND (Rabs a * Rabs b) zi ->
 true = true ->
 BND (Rabs (a * b)) zi.
intros a b zi Hz _.
rewrite Rabs_mult.
exact Hz.
Qed.

End Gappa_rewriting.
