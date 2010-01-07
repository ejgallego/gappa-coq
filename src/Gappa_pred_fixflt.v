Require Import Gappa_common.
Require Import Gappa_integer.
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
do 2 rewrite Zpower_pos_powerRZ.
do 2 rewrite <- float2_pow2.
apply float2_Rle_pow2.
exact H.
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
intros x xi n p (f,(Hx1,Hx2)) Hxi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
exists f.
split.
exact Hx1.
apply Znot_gt_le.
intro H0.
apply Zle_not_gt with (1 := H1).
clear H1.
apply Zlt_gt.
cut (Fexp (lower xi) + Zpos (digits (pos_of_Z (Fnum (lower xi)))) - 1 <
  Fexp f + Zpos p)%Z.
omega.
clear H0.
assert (He1: (Float2 (Zabs (Fnum f)) (Fexp f) = Rabs x :>R)).
rewrite <- Hx1.
unfold float2R. simpl.
do 2 rewrite F2R_split.
rewrite Rabs_mult.
rewrite (Rabs_right (powerRZ (P2R 2) (Fexp f))).
do 2 rewrite <- (Rmult_comm (powerRZ 2 (Fexp f))).
apply Rmult_eq_compat_l.
do 2 rewrite Z2R_IZR.
apply sym_eq.
apply Rabs_Zabs.
apply Rle_ge.
apply Rlt_le.
apply power_radix_pos.
assert (He2: (Zpos (pos_of_Z (Zabs (Fnum f))) = Zabs (Fnum f))%Z).
apply Zpos_pos_of_Z.
apply float2_pos_reg with (Fexp f).
apply Rlt_le_trans with (1 := H2).
rewrite He1.
exact (proj1 (proj2 Hxi)).
apply Zlt_le_trans with (Fexp f + Zpos (digits (pos_of_Z (Zabs (Fnum f)))))%Z.
apply float2_pow2_lt.
apply Rle_lt_trans with (2 := proj2 (float2_digits_correct (pos_of_Z (Zabs (Fnum f))) (Fexp f))).
apply Rle_trans with (1 := proj1 (float2_digits_correct (pos_of_Z (Fnum (lower xi))) (Fexp (lower xi)))).
cutrewrite (Float2 (Zpos (pos_of_Z (Fnum (lower xi)))) (Fexp (lower xi)) = lower xi).
cutrewrite (Float2 (Zpos (pos_of_Z (Zabs (Fnum f)))) (Fexp f) = Rabs x :>R).
exact (proj1 (proj2 Hxi)).
rewrite He2.
exact He1.
cutrewrite (Zpos (pos_of_Z (Fnum (lower xi))) = Fnum (lower xi)).
case (lower xi). intros. exact (refl_equal _).
apply Zpos_pos_of_Z.
apply float2_pos_reg with (Fexp (lower xi)).
exact H2.
apply Zplus_le_compat_l.
apply digits_pow2.
rewrite He2.
exact Hx2.
Qed.

Theorem flt_of_fix_bnd :
 forall x : R, forall xi : FF, forall n : Z, forall p : positive,
 FIX x n -> ABS x xi ->
 Zle_bool (Zpos (digits (pos_of_Z (Fnum (upper xi)))) + Fexp (upper xi)) (n + Zpos p) = true ->
 FLT x p.
intros x xi n p (f,(Hx1,Hx2)) Hxi H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
exists f.
split.
exact Hx1.
apply Znot_ge_lt.
intro H0.
apply Zle_not_gt with (1 := H).
clear H.
assert (Float2 1 (n + Zpos p) <= upper xi)%R.
apply Rle_trans with (2 := proj2 (proj2 Hxi)).
rewrite <- Hx1.
apply Rle_trans with (float2R (Float2 (Zabs (Fnum f)) n)).
cutrewrite (Float2 1 (n + Zpos p) = Float2 (Zpower_pos 2 p) n :>R)%R.
exact (float2_binade_le _ _ _ (Zge_le _ _ H0)).
unfold float2R. simpl.
do 2 rewrite F2R_split.
rewrite Rmult_1_l.
rewrite powerRZ_add.
apply sym_eq.
rewrite Rmult_comm.
apply Rmult_eq_compat_l.
exact (Zpower_pos_powerRZ _ _).
apply Rgt_not_eq.
exact (Z2R_lt 0 2 (refl_equal _)).
unfold float2R. simpl.
do 2 rewrite F2R_split.
rewrite Rabs_mult.
rewrite (Rabs_right (powerRZ (P2R 2) (Fexp f))).
do 2 rewrite Z2R_IZR.
rewrite Rabs_Zabs.
apply Rmult_le_compat_l.
apply (IZR_le 0).
apply Zabs_pos.
assert (Float2 1 n <= Float2 1 (Fexp f))%R.
apply float2_Rle_pow2.
exact Hx2.
unfold float2R in H.
simpl in H.
do 2 rewrite F2R_split in H.
apply Rmult_le_reg_l with (2 := H).
exact (Z2R_lt 0 1 (refl_equal _)).
apply Rle_ge.
apply Rlt_le.
apply power_radix_pos.
apply Zlt_gt.
apply float2_pow2_lt.
apply Rle_lt_trans with (1 := H).
assert (0 <= upper xi)%R.
apply Rle_trans with (1 := proj1 Hxi).
apply Rle_trans with (1 := proj1 (proj2 Hxi)).
exact (proj2 (proj2 Hxi)).
destruct H1.
assert (upper xi = Float2 (Zpos (pos_of_Z (Fnum (upper xi)))) (Fexp (upper xi))).
rewrite Zpos_pos_of_Z.
case (upper xi). intros. exact (refl_equal _).
apply float2_pos_reg with (Fexp (upper xi)).
exact H1.
pattern (upper xi) at 1 ; rewrite H2.
rewrite Zplus_comm.
exact (proj2 (float2_digits_correct _ _)).
rewrite <- H1.
apply float2_pos_compat.
split.
Qed.

End Gappa_pred_fixflt.
