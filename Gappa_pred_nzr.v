Require Import Gappa_common.

Section Gappa_pred_nzr.

Lemma nzr_of_abs :
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

Lemma nzr_of_bnd_p :
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

Lemma nzr_of_bnd_n :
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

End Gappa_pred_nzr.
