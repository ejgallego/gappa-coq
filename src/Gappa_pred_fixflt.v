Require Import Fcore_defs.
Require Import Fcore_float_prop.
Require Import Gappa_common.
Require Import Gappa_round_aux.

Section Gappa_pred_fixflt.

Theorem fix_subset :
 forall x : R, forall xn zn : Z,
 FIX x xn ->
 Zle_bool zn xn = true ->
 FIX x zn.
intros x xn zn (xf,(Hx1,Hx2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H.
exists xf.
split.
exact Hx1.
apply Zle_trans with (1 := H) (2 := Hx2).
Qed.

Theorem flt_subset :
 forall x : R, forall xn zn : positive,
 FLT x xn ->
 Zle_bool (Zpos xn) (Zpos zn) = true ->
 FLT x zn.
intros x xn zn (xf,(Hx1,Hx2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H.
exists xf.
split.
exact Hx1.
apply Zlt_le_trans with (1 := Hx2).
apply le_Z2R.
change (Z2R (Zpower radix2 (Zpos xn)) <= Z2R (Zpower radix2 (Zpos zn)))%R.
rewrite 2!Z2R_Zpower ; try apply bpow_le ; easy.
Qed.

Definition fix_of_singleton_bnd_helper (xi : FF) (n : Z) :=
 Zeq_bool (Fnum (lower xi)) (Fnum (upper xi)) &&
 Zeq_bool (Fexp (lower xi)) (Fexp (upper xi)) &&
 Zle_bool n (Fexp (lower xi)).

Theorem fix_of_singleton_bnd :
 forall x : R, forall xi : FF, forall n : Z,
 ABS x xi ->
 fix_of_singleton_bnd_helper xi n = true ->
 FIX x n.
intros x xi n (_, (Hx1, Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zeq_bool_correct_t _ _ H1). clear H1. intro H1.
generalize (Zeq_bool_correct_t _ _ H2). clear H2. intro H2.
generalize (Zle_bool_imp_le _ _ H3). clear H3. intro H3.
assert (float2R (lower xi) = Rabs x).
apply Rle_antisym.
exact Hx1.
replace (lower xi) with (upper xi).
exact Hx2.
apply sym_equal.
induction (lower xi). induction (upper xi).
exact (f_equal2 _ H1 H2).
unfold Rabs in H.
induction (Rcase_abs x).
exists (Fopp2 (lower xi)).
split.
rewrite Fopp2_correct.
rewrite <- (Ropp_involutive x).
apply Ropp_eq_compat.
exact H.
exact H3.
exists (lower xi).
exact (conj H H3).
Qed.

Definition flt_of_singleton_bnd_helper (xi : FF) (n : positive) :=
 Zeq_bool (Fnum (lower xi)) (Fnum (upper xi)) &&
 Zeq_bool (Fexp (lower xi)) (Fexp (upper xi)) &&
 Zlt_bool (Zabs (Fnum (lower xi))) (two_power_pos n).

Theorem flt_of_singleton_bnd :
 forall x : R, forall xi : FF, forall n : positive,
 ABS x xi ->
 flt_of_singleton_bnd_helper xi n = true ->
 FLT x n.
intros x xi n (_, (Hx1, Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zeq_bool_correct_t _ _ H1). clear H1. intro H1.
generalize (Zeq_bool_correct_t _ _ H2). clear H2. intro H2.
generalize (Zlt_cases (Zabs (Fnum (lower xi))) (two_power_pos n)). rewrite H3. rewrite two_power_pos_correct. clear H3. intro H3.
assert (float2R (lower xi) = Rabs x).
apply Rle_antisym.
exact Hx1.
replace (lower xi) with (upper xi).
exact Hx2.
apply sym_equal.
induction (lower xi). induction (upper xi).
exact (f_equal2 _ H1 H2).
unfold Rabs in H.
induction (Rcase_abs x).
exists (Fopp2 (lower xi)).
split.
rewrite Fopp2_correct.
rewrite <- (Ropp_involutive x).
apply Ropp_eq_compat.
exact H.
simpl.
rewrite Zabs_Zopp.
exact H3.
exists (lower xi).
exact (conj H H3).
Qed.

Definition add_fix_helper (xn yn zn : Z) :=
 Zle_bool zn xn &&
 Zle_bool zn yn.

Theorem add_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x + y)%R zn.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
exists (Fplus2 fx fy).
split.
rewrite <- Hx1.
rewrite <- Hy1.
apply Fplus2_correct.
unfold Fplus2, Fshift2.
case (Fexp fx - Fexp fy)%Z ; intros.
exact (Zle_trans _ _ _ H1 Hx2).
exact (Zle_trans _ _ _ H2 Hy2).
exact (Zle_trans _ _ _ H1 Hx2).
Qed.

Theorem sub_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x - y)%R zn.
intros x y xn yn zn Hx (fy,(Hy1,Hy2)) Hb.
unfold Rminus.
apply (add_fix _ (-y) _ yn zn Hx).
exists (Fopp2 fy).
split.
rewrite <- Hy1.
apply Fopp2_correct.
exact Hy2.
exact Hb.
Qed.

Theorem mul_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 Zle_bool zn (xn + yn) = true ->
 FIX (x * y)%R zn.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Fmult2 fx fy).
split.
rewrite <- Hx1. rewrite <- Hy1.
apply Fmult2_correct.
apply Zle_trans with (1 := H1).
exact (Zplus_le_compat _ _ _ _ Hx2 Hy2).
Qed.

Theorem mul_flt :
 forall x y : R, forall xn yn zn : positive,
 FLT x xn -> FLT y yn ->
 Zle_bool (Zpos xn + Zpos yn) (Zpos zn) = true ->
 FLT (x * y)%R zn.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Fmult2 fx fy).
split.
rewrite <- Hx1. rewrite <- Hy1.
apply Fmult2_correct.
apply Zlt_le_trans with (Zpower_nat 2 (nat_of_P xn + nat_of_P yn)).
rewrite Zpower_nat_is_exp.
simpl.
rewrite Zabs_Zmult.
repeat rewrite <- Zpower_pos_nat.
apply Zle_lt_trans with (Zabs (Fnum fx) * Zpower_pos 2 yn)%Z.
exact (Zmult_le_compat_l _ _ _ (Zlt_le_weak _ _ Hy2) (Zabs_pos (Fnum fx))).
apply Zmult_lt_compat_r with (2 := Hx2).
rewrite Zpower_pos_nat.
unfold Zpower_nat.
set (f := fun x0 : Z => (2 * x0)%Z).
induction (nat_of_P yn).
exact (refl_equal _).
simpl.
unfold f at 1.
omega.
rewrite Zpower_pos_nat.
assert (nat_of_P xn + nat_of_P yn <= nat_of_P zn).
case (le_or_lt (nat_of_P xn + nat_of_P yn) (nat_of_P zn)) ; intro.
exact H.
elim (Zle_not_lt _ _ H1).
repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite <- inj_plus.
exact (inj_lt _ _ H).
rewrite (le_plus_minus _ _ H).
generalize (nat_of_P xn + nat_of_P yn).
intros.
rewrite Zpower_nat_is_exp.
pattern (Zpower_nat 2 n) at 1 ; replace (Zpower_nat 2 n) with (Zpower_nat 2 n * 1)%Z.
2: apply Zmult_1_r.
apply Zmult_le_compat_l.
unfold Zpower_nat.
set (f := fun x0 : Z => (2 * x0)%Z).
induction (nat_of_P zn - n).
apply Zle_refl.
simpl.
unfold f at 1.
omega.
apply Zpower_NR0.
compute.
discriminate.
Qed.

Theorem fix_of_flt_bnd :
 forall x : R, forall xi : FF, forall n : Z, forall p : positive,
 FLT x p -> ABS x xi ->
 Zle_bool (n + Zpos p) (Zpos (digits (pos_of_Z (Fnum (lower xi)))) + Fexp (lower xi))
 && Fpos (lower xi) = true ->
 FIX x n.
Proof.
intros x ((ml,el),xu) n p ((mx,ex),(Hx1,Hx2)) (_,(Hxi,_)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). simpl Fnum. simpl Fexp. clear H1. intro H1.
generalize (Fpos_correct _ H2). simpl. clear H2. intro H2.
exists (Float2 mx ex).
split.
exact Hx1.
apply Zplus_le_reg_l with (Zpos p).
rewrite Zplus_comm.
apply Zle_trans with (1 := H1). clear H1.
rewrite digits2_digits.
assert (H0: (0 < ml)%Z).
apply F2R_gt_0_reg with (1 := H2).
rewrite Zpos_pos_of_Z with (1 := H0).
assert (H0': ml <> Z0).
intros H.
now rewrite H in H0.
rewrite Fcalc_digits.digits_ln_beta with (1 := H0').
rewrite <- ln_beta_F2R with (1 := H0').
apply Zle_trans with (ln_beta radix2 (Rabs (Float2 mx ex))).
apply ln_beta_monotone.
now apply F2R_gt_0_compat.
now rewrite Hx1.
rewrite ln_beta_abs.
unfold float2R.
assert (Hx0: mx <> Z0).
intros H.
apply Rle_not_lt with (1 := Hxi).
rewrite <- Hx1, H.
unfold float2R.
rewrite F2R_0, Rabs_R0.
now apply F2R_gt_0_compat.
rewrite ln_beta_F2R with (1 := Hx0).
apply Zplus_le_compat_r.
destruct (ln_beta radix2 (Z2R mx)) as (e, He).
simpl.
apply bpow_lt_bpow with radix2.
apply Rle_lt_trans with (Rabs (Z2R mx)).
apply He.
now apply (Z2R_neq _ 0).
rewrite <- Z2R_abs.
rewrite <- Z2R_Zpower. 2: easy.
now apply Z2R_lt.
Qed.

Theorem flt_of_fix_bnd :
  forall x xi n p,
  FIX x n -> ABS x xi ->
  Zle_bool (Zpos (digits (pos_of_Z (Fnum (upper xi)))) + Fexp (upper xi)) (n + Zpos p) = true ->
  FLT x p.
Proof.
intros x (xl,(mu,eu)) n p ((m,e),(Hx1,Hx2)) Hxi H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
exists (Float2 m e).
split.
exact Hx1.
unfold float2R in Hx1. simpl in Hx1.
simpl Fnum in H. simpl Fexp in H.
apply (F2R_lt_reg radix2 e).
rewrite <- abs_F2R.
apply Rle_lt_trans with (F2R (Float radix2 mu eu)).
simpl. rewrite Hx1.
apply Hxi.
apply Rlt_le_trans with (bpow radix2 (n + Zpos p)).
destruct (Zle_or_lt mu 0) as [Hu|Hu].
apply Rle_lt_trans with R0.
now apply F2R_le_0_compat.
apply bpow_gt_0.
apply Rlt_le_trans with (bpow radix2 (Fcalc_digits.digits radix2 mu + eu)).
rewrite Fcalc_digits.digits_ln_beta. 2: intros Hu' ; now rewrite Hu' in Hu.
rewrite <- ln_beta_F2R. 2: intros Hu' ; now rewrite Hu' in Hu.
destruct (ln_beta radix2 (F2R (Float radix2 mu eu))) as (e', He).
apply (Rle_lt_trans _ _ _ (RRle_abs _)).
apply He.
apply Rgt_not_eq.
now apply F2R_gt_0_compat.
rewrite <- (Zpos_pos_of_Z _ Hu).
rewrite <- digits2_digits.
now apply bpow_le.
unfold F2R. simpl.
change (Zpower_pos 2 p) with (Zpower radix2 (Zpos p)).
rewrite Z2R_Zpower. 2: easy.
rewrite <- bpow_plus.
apply bpow_le.
rewrite Zplus_comm.
now apply Zplus_le_compat_l.
Qed.

End Gappa_pred_fixflt.
