Require Import Gappa_common.

Section Gappa_pred_nzr.

Theorem nzr_of_abs :
 forall z : R, forall zi : FF,
 ABS z zi ->
 Fpos (lower zi) = true ->
 NZR z.
intros z zi Hz Hb.
generalize (Fpos_correct _ Hb). clear Hb. intro H.
case (Rcase_abs z) ; intro.
apply Rlt_not_eq with (1 := r).
rewrite <- (Rabs_right z r).
unfold NZR.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H) (2 := proj1 (proj2 Hz)).
Qed.

Theorem nzr_of_bnd_p :
 forall z : R, forall zi : FF,
 BND z zi ->
 Fpos (lower zi) = true ->
 NZR z.
intros z zi Hz Hb.
generalize (Fpos_correct _ Hb). clear Hb. intro H.
unfold NZR.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H) (2 := proj1 Hz).
Qed.

Theorem nzr_of_bnd_n :
 forall z : R, forall zi : FF,
 BND z zi ->
 Fneg (upper zi) = true ->
 NZR z.
intros z zi Hz Hb.
generalize (Fneg_correct _ Hb). clear Hb. intro H.
unfold NZR.
apply Rlt_not_eq.
apply Rle_lt_trans with (1 := proj2 Hz) (2 := H).
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
  Flt2_m1 (lower zi) = true ->
  NZR zr.
Proof.
intros z zr zi Hn (ze,(Hz1,Hz2)) H1.
assert (1 + ze <> 0)%R.
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (1 + lower zi)%R.
replace R0 with (1 + -1)%R. 2: ring.
apply Rplus_lt_compat_l.
now apply Flt2_m1_correct.
apply Rplus_le_compat_l.
apply Hz1.
replace zr with (z * /(1 + ze))%R.
unfold NZR.
apply prod_neq_R0.
exact Hn.
now apply Rinv_neq_0_compat.
rewrite Hz2.
now field.
Qed.

End Gappa_pred_nzr.
