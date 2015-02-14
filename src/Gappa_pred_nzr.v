Require Import Gappa_common.

Theorem neg_nzr :
  forall x : R,
  NZR x ->
  NZR (-x).
Proof.
unfold NZR.
intros x Hx.
contradict Hx.
rewrite <- (Ropp_involutive x), Hx.
apply Ropp_0.
Qed.

Theorem mul_nzr :
  forall x y : R,
  NZR x -> NZR y ->
  NZR (x * y).
Proof.
intros x y Hx Hy.
apply Rmult_integral_contrapositive.
now split.
Qed.

Theorem div_nzr :
  forall x y : R,
  NZR x -> NZR y ->
  NZR (x / y).
Proof.
intros x y Hx Hy.
apply Rmult_integral_contrapositive.
split.
exact Hx.
now apply Rinv_neq_0_compat.
Qed.

Theorem nzr_of_abs :
  forall z : R, forall zi : FF,
  ABS z zi ->
  Fpos (lower zi) = true ->
  NZR z.
Proof.
intros z zi Hz Hb.
generalize (Fpos_correct _ Hb). clear Hb. intro H.
case (Rcase_abs z) ; intro.
apply Rlt_not_eq with (1 := r).
rewrite <- (Rabs_right z r).
unfold NZR.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H) (2 := proj1 (proj2 Hz)).
Qed.

Theorem nzr_of_nzr_rel :
  forall z zr : R, forall zi : FF,
  NZR zr ->
  REL z zr zi ->
  Flt2_m1 (lower zi) = true ->
  NZR z.
Proof.
intros z zr zi Hn (ze,(Hz1,Hz2)) H1.
apply Flt2_m1_correct in H1.
rewrite Hz2.
apply prod_neq_R0.
exact Hn.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 + lower zi)%R.
rewrite <- (Rplus_opp_r 1).
apply Rplus_lt_compat_l.
exact H1.
apply Rplus_le_compat_l.
apply Hz1.
Qed.

Theorem nzr_of_nzr_rel_rev :
  forall z zr : R, forall zi : FF,
  NZR z ->
  REL z zr zi ->
  NZR zr.
Proof.
intros z zr zi Hn (ze,(Hz1,Hz2)) H1.
apply Hn.
rewrite Hz2, H1.
apply Rmult_0_l.
Qed.
