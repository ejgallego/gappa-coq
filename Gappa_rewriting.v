Require Import Reals.
Require Import Gappa_common.

Section Gappa_rewriting.

Theorem opp_mibs :
 forall a b : R, forall zi : FF,
 BND (-a - -b) zi ->
 BND (-(a - b)) zi.
intros a b zi Hz.
replace (-(a - b))%R with (-a - -b)%R.
exact Hz.
ring.
Qed.

Theorem opp_mibq :
 forall a b : R, forall bi zi : FF,
 ABS b bi ->
 BND ((-a - -b) / -b) zi ->
 abs_not_zero bi = true ->
 BND ((a - b) / b) zi.
intros a b bi zi Hb Hz H.
generalize (abs_not_zero_correct _ _ Hb H). clear H. intro H.
replace ((a - b) / b)%R with ((-a - -b) / -b)%R.
exact Hz.
field.
auto with real.
Qed.

Theorem add_xals :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + (c + b)) zi ->
 BND (a + b) zi.
intros a b c zi Hz.
replace (a + b)%R with ((a - c) + (c + b))%R.
exact Hz.
ring.
Qed.

Theorem add_xars :
 forall a b c : R, forall zi : FF,
 BND ((a + c) + (b - c)) zi ->
 BND (a + b) zi.
intros a b c zi Hz.
replace (a + b)%R with ((a + c) + (b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_xals :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + (c - b)) zi ->
 BND (a - b) zi.
intros a b c zi Hz.
replace (a - b)%R with ((a - c) + (c - b))%R.
exact Hz.
ring.
Qed.

Theorem sub_xars :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + -(b - c)) zi ->
 BND (a - b) zi.
intros a b c zi Hz.
replace (a - b)%R with ((a - c) + -(b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_xals :
 forall a b c : R, forall zi : FF,
 BND ((a - c) * b + c * b) zi ->
 BND (a * b) zi.
intros a b c zi Hz.
replace (a * b)%R with ((a - c) * b + c * b)%R.
exact Hz.
ring.
Qed.

Theorem mul_xars :
 forall a b c : R, forall zi : FF,
 BND (a * (b - c) + a * c) zi ->
 BND (a * b) zi.
intros a b c zi Hz.
replace (a * b)%R with (a * (b - c) + a * c)%R.
exact Hz.
ring.
Qed.

Theorem add_mibs :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) + (b - d)) zi ->
 BND ((a + b) - (c + d)) zi.
intros a b c d zi Hz.
replace ((a + b) - (c + d))%R with ((a - c) + (b - d))%R.
exact Hz.
ring.
Qed.

Theorem add_fils :
 forall a b c : R, forall zi : FF,
 BND (b - c) zi ->
 BND ((a + b) - (a + c)) zi.
intros a b c zi Hz.
replace ((a + b) - (a + c))%R with (b - c)%R.
exact Hz.
ring.
Qed.

Theorem add_firs :
 forall a b c : R, forall zi : FF,
 BND (a - c) zi ->
 BND ((a + b) - (c + b)) zi.
intros a b c zi Hz.
replace ((a + b) - (c + b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem sub_mibs :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) + -(b - d)) zi ->
 BND ((a - b) - (c - d)) zi.
intros a b c d zi Hz.
replace ((a - b) - (c - d))%R with ((a - c) + -(b - d))%R.
exact Hz.
ring.
Qed.

Theorem sub_fils :
 forall a b c : R, forall zi : FF,
 BND (-(b - c)) zi ->
 BND ((a - b) - (a - c)) zi.
intros a b c zi Hz.
replace ((a - b) - (a - c))%R with (-(b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_firs :
 forall a b c : R, forall zi : FF,
 BND (a - c) zi ->
 BND ((a - b) - (c - b)) zi.
intros a b c zi Hz.
replace ((a - b) - (c - b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem mul_fils :
 forall a b c : R, forall zi : FF,
 BND (a * (b - c)) zi ->
 BND (a * b - a * c) zi.
intros a b c zi Hz.
replace (a * b - a * c)%R with (a * (b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_firs :
 forall a b c : R, forall zi : FF,
 BND ((a - c) * b) zi ->
 BND (a * b - c * b) zi.
intros a b c zi Hz.
replace (a * b - c * b)%R with ((a - c) * b)%R.
exact Hz.
ring.
Qed.

Theorem mul_mars :
 forall a b c d : R, forall zi : FF,
 BND (a * (b - d) + (a - c) * d) zi ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * d)%R.
exact Hz.
ring.
Qed.

Theorem mul_mals :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) * b + c * (b - d)) zi ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz.
replace (a * b - c * d)%R with ((a - c) * b + c * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem mul_mabs :
 forall a b c d : R, forall zi : FF,
 BND (a * (b - d) + (a - c) * b + -((a - c) * (b - d))) zi ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * b + -((a - c) * (b - d)))%R.
exact Hz.
ring.
Qed.

Theorem mul_mibs :
 forall a b c d : R, forall zi : FF,
 BND (c * (b - d) + (a - c) * d + (a - c) * (b - d)) zi ->
 BND (a * b - c * d) zi.
intros a b c d zi Hz.
replace (a * b - c * d)%R with (c * (b - d) + (a - c) * d + (a - c) * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem err_xibq :
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

Theorem err_xalq :
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

Theorem mul_mibq :
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
exact (conj Hd Hc).
Qed.

Theorem mul_filq :
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
exact (conj Hc Ha).
Qed.

Theorem mul_firq :
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
exact (conj Hb Hc).
Qed.

Theorem sqrt_mibs :
 forall a b : R, forall ai bi zi : FF,
 BND a ai -> BND b bi ->
 BND ((a - b) / (sqrt a + sqrt b)) zi ->
 Fpos0 (lower ai) && Fpos0 (lower bi) = true ->
 BND (sqrt a - sqrt b) zi.
intros a b ai bi zi Ha Hb Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
assert (H3: (0 <= sqrt a)%R).
apply sqrt_positivity.
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
assert (H4: (0 <= sqrt b)%R).
apply sqrt_positivity.
apply Rle_trans with (1 := H2) (2 := proj1 Hb).
case (Rtotal_order (sqrt a + sqrt b) 0).
intro H. elim Rlt_not_le with (1 := H).
apply Rplus_le_le_0_compat ; assumption.
intros [H|H] ;
replace (sqrt a - sqrt b)%R with ((a - b) / (sqrt a + sqrt b))%R ;
try exact Hz.
assert (sqrt a = 0)%R.
apply Rle_antisym. 2: exact H3.
rewrite <- H.
pattern (sqrt a) at 1 ; rewrite <- (Rplus_0_r (sqrt a)).
apply Rplus_le_compat_l with (1 := H4).
rewrite H0 in H.
rewrite Rplus_0_l in H.
rewrite H. rewrite H0.
cutrewrite (a = 0)%R.
cutrewrite (b = 0)%R.
rewrite Rminus_0_r.
unfold Rdiv.
apply Rmult_0_l.
apply sqrt_eq_0 with (2 := H).
apply Rle_trans with (1 := H2) (2 := proj1 Hb).
apply sqrt_eq_0 with (2 := H0).
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
replace (a - b)%R with (sqrt a * sqrt a - sqrt b * sqrt b)%R.
field.
auto with real.
repeat rewrite sqrt_def.
exact (refl_equal _).
apply Rle_trans with (1 := H2) (2 := proj1 Hb).
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
Qed.

Theorem sqrt_mibq :
 forall a b : R, forall ai bi zi : FF,
 BND a ai -> BND b bi ->
 BND (sqrt (1 + (a - b) / b) - 1) zi ->
 Fpos0 (lower ai) && Fpos (lower bi) = true ->
 BND ((sqrt a - sqrt b) / sqrt b) zi.
intros a b ai bi zi Ha Hb Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
replace ((sqrt a - sqrt b) / sqrt b)%R with (sqrt (1 + (a - b) / b) - 1)%R.
exact Hz.
replace (1+ (a - b) / b)%R with (a / b)%R.
rewrite sqrt_div.
field.
apply Rgt_not_eq.
unfold Rgt.
apply sqrt_lt_R0.
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
field.
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
Qed.

Theorem abs_mul_xx :
 forall a b : R, forall zi : FF,
 BND (Rabs a * Rabs b) zi ->
 BND (Rabs (a * b)) zi.
intros a b zi Hz.
rewrite Rabs_mult.
exact Hz.
Qed.

Theorem val_xebs :
 forall a b : R, forall zi : FF,
 BND (b + -(b - a)) zi ->
 BND a zi.
intros a b zi Hz.
replace a with (b + -(b - a))%R.
exact Hz.
ring.
Qed.

Theorem val_xabs :
 forall a b : R, forall zi : FF,
 BND (a + (b - a)) zi ->
 BND b zi.
intros a b zi Hz.
replace b with (a + (b - a))%R.
exact Hz.
ring.
Qed.

Theorem val_xebq :
 forall a b : R, forall ai bi zi : FF,
 ABS a ai -> ABS b bi ->
 BND (b / (1 + (b - a) / a)) zi ->
 abs_not_zero ai && abs_not_zero bi = true ->
 BND a zi.
intros a b ai ci zi Ha Hb Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Ha H1). clear Ha H1. intro Ha.
generalize (abs_not_zero_correct _ _ Hb H2). clear Hb H2. intro Hb.
replace a with (b / (1 + (b - a) / a))%R.
exact Hz.
field.
replace (a + (b - a))%R with b. 2: ring.
exact (conj Ha Hb).
Qed.

Theorem val_xabq :
 forall a b : R, forall ai zi : FF,
 ABS a ai ->
 BND (a * (1 + (b - a) / a)) zi ->
 abs_not_zero ai = true ->
 BND b zi.
intros a b ai zi Ha Hz H.
generalize (abs_not_zero_correct _ _ Ha H). clear Ha H. intro Ha.
replace b with (a * (1 + (b - a) / a))%R.
exact Hz.
field.
exact Ha.
Qed.

Theorem div_mibq :
 forall a b c d : R, forall bi ci di zi : FF,
 ABS b bi -> ABS c ci -> ABS d di ->
 BND (((a - c) / c - (b - d) / d) / (1 + (b - d) / d)) zi ->
 abs_not_zero bi && abs_not_zero ci && abs_not_zero di = true ->
 BND ((a / b - c / d) / (c / d)) zi.
intros a b c d bi ci di zi Hb Hc Hd Hz H.
generalize (andb_prop _ _ H). clear H. intros (H, H3).
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Hb H1). clear Hb H1. intro Hb.
generalize (abs_not_zero_correct _ _ Hc H2). clear Hc H2. intro Hc.
generalize (abs_not_zero_correct _ _ Hd H3). clear Hd H3. intro Hd.
replace ((a / b - c / d) / (c / d))%R with (((a - c) / c - (b - d) / d) / (1 + (b - d) / d))%R.
exact Hz.
field.
exact (conj Hd (conj Hb Hc)).
Qed.

Theorem div_firq :
 forall a b c : R, forall bi ci zi : FF,
 ABS b bi -> ABS c ci ->
 BND ((a - c) / c) zi ->
 abs_not_zero bi && abs_not_zero ci = true ->
 BND ((a / b - c / b) / (c / b)) zi.
intros a b c bi ci zi Hb Hc Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1, H2).
generalize (abs_not_zero_correct _ _ Hb H1). clear Hb H1. intro Hb.
generalize (abs_not_zero_correct _ _ Hc H2). clear Hc H2. intro Hc.
replace ((a / b - c / b) / (c / b))%R with ((a - c) / c)%R.
exact Hz.
field.
exact (conj Hb Hc).
Qed.

Theorem err_xabq :
 forall a b : R, forall bi zi : FF,
 ABS b bi -> BND (1 + (a - b) / b) zi ->
 abs_not_zero bi = true ->
 BND (a / b) zi.
intros a b bi zi Hb Hz H.
generalize (abs_not_zero_correct _ _ Hb H). clear Hb H. intro H.
replace (a / b)%R with (1 + (a - b) / b)%R.
exact Hz.
field.
exact H.
Qed.

Theorem err_fabq :
 forall a b : R, forall bi zi : FF,
 ABS b bi -> BND (a / b) zi ->
 abs_not_zero bi = true ->
 BND (1 + (a - b) / b) zi.
intros a b bi zi Hb Hz H.
generalize (abs_not_zero_correct _ _ Hb H). clear Hb H. intro H.
replace (1 + (a - b) / b)%R with (a / b)%R .
exact Hz.
field.
exact H.
Qed.

End Gappa_rewriting.
