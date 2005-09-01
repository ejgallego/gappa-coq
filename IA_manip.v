Require Import IA_real.
Require Import IA_comput.

Section IA_manip.

Theorem add_decomposition_rounded_left :
 forall a b c : R, forall zi : FF,
 IintF zi ((a - c) + (c + b)) ->
 true = true ->
 IintF zi (a + b).
intros a b c zi Hz _.
replace (a + b)%R with ((a - c) + (c + b))%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition_rounded_right :
 forall a b c : R, forall zi : FF,
 IintF zi ((a + c) + (b - c)) ->
 true = true ->
 IintF zi (a + b).
intros a b c zi Hz _.
replace (a + b)%R with ((a + c) + (b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_rounded_left :
 forall a b c : R, forall zi : FF,
 IintF zi ((a - c) + (c - b)) ->
 true = true ->
 IintF zi (a - b).
intros a b c zi Hz _.
replace (a - b)%R with ((a - c) + (c - b))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_rounded_right :
 forall a b c : R, forall zi : FF,
 IintF zi ((a - c) + -(b - c)) ->
 true = true ->
 IintF zi (a - b).
intros a b c zi Hz _.
replace (a - b)%R with ((a - c) + -(b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_rounded_left :
 forall a b c : R, forall zi : FF,
 IintF zi ((a - c) * b + c * b) ->
 true = true ->
 IintF zi (a * b).
intros a b c zi Hz _.
replace (a * b)%R with ((a - c) * b + c * b)%R.
exact Hz.
ring.
Qed.

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

Theorem add_decomposition_left :
 forall a b c : R, forall zi : FF,
 IintF zi (b - c) ->
 true = true ->
 IintF zi ((a + b) - (a + c)).
intros a b c zi Hz _.
replace ((a + b) - (a + c))%R with (b - c)%R.
exact Hz.
ring.
Qed.

Theorem add_decomposition_right :
 forall a b c : R, forall zi : FF,
 IintF zi (a - c) ->
 true = true ->
 IintF zi ((a + b) - (c + b)).
intros a b c zi Hz _.
replace ((a + b) - (c + b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition :
 forall a b c d : R, forall zi : FF,
 IintF zi ((a - c) + -(b - d)) ->
 true = true ->
 IintF zi ((a - b) - (c - d)).
intros a b c d zi Hz _.
replace ((a - b) - (c - d))%R with ((a - c) + -(b - d))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_left :
 forall a b c : R, forall zi : FF,
 IintF zi (-(b - c)) ->
 true = true ->
 IintF zi ((a - b) - (a - c)).
intros a b c zi Hz _.
replace ((a - b) - (a - c))%R with (-(b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition_right :
 forall a b c : R, forall zi : FF,
 IintF zi (a - c) ->
 true = true ->
 IintF zi ((a - b) - (c - b)).
intros a b c zi Hz _.
replace ((a - b) - (c - b))%R with (a - c)%R.
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

Theorem mul_decomposition_factor_right :
 forall a b c : R, forall zi : FF,
 IintF zi ((a - c) * b) ->
 true = true ->
 IintF zi (a * b - c * b).
intros a b c zi Hz _.
replace (a * b - c * b)%R with ((a - c) * b)%R.
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
 IintF bi (Rabs b) -> IintF zi (a / b * b) ->
 abs_not_zero bi = true ->
 IintF zi a.
intros a b bi zi Hb Hz H.
generalize (abs_not_zero_correct _ _ Hb H). clear Hb H. intro H.
replace a with (a / b * b)%R.
exact Hz.
field.
exact H.
Qed.

Theorem relative_transitivity :
 forall a b c : R, forall bi ci zi : FF,
 IintF bi (Rabs b) -> IintF ci (Rabs c) ->
 IintF zi ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b)) ->
 abs_not_zero bi && abs_not_zero ci = true ->
 IintF zi ((a - b) / b).
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
 IintF ci (Rabs c) -> IintF di (Rabs d) ->
 IintF zi ((a - c) / c + (b - d) / d + ((a - c) / c) * ((b - d) / d)) ->
 abs_not_zero ci && abs_not_zero di = true ->
 IintF zi ((a * b - c * d) / (c * d)).
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
 IintF ai (Rabs a) -> IintF ci (Rabs c) ->
 IintF zi ((b - c) / c) ->
 abs_not_zero ai && abs_not_zero ci = true ->
 IintF zi ((a * b - a * c) / (a * c)).
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
 IintF bi (Rabs b) -> IintF ci (Rabs c) ->
 IintF zi ((a - c) / c) ->
 abs_not_zero bi && abs_not_zero ci = true ->
 IintF zi ((a * b - c * b) / (c * b)).
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
 IintF zi (Rabs a * Rabs b) ->
 true = true ->
 IintF zi (Rabs (a * b)).
intros a b zi Hz _.
rewrite Rabs_mult.
exact Hz.
Qed.

End IA_manip.
