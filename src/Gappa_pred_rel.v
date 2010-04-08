Require Import Gappa_common.
Require Import Gappa_pred_bnd.

Section Gappa_pred_rel.

Theorem bnd_of_nzr_rel :
 forall a b : R, forall zi : FF,
 NZR b -> REL a b zi ->
 BND ((a - b) / b) zi.
intros a b zi Hb (x,(Hr1,Hr2)).
cutrewrite ((a - b) / b = x)%R.
exact Hr1.
rewrite Hr2.
field.
exact Hb.
Qed.

Theorem rel_of_nzr_bnd :
  forall a b : R, forall zi : FF,
  NZR b -> BND ((a - b) / b) zi ->
  REL a b zi.
Proof.
intros a b zi Hb Hr.
exists ((a - b) / b)%R.
split.
exact Hr.
now field.
Qed.

Definition rel_of_equal_helper xi zi :=
  Fneg0 (lower zi) &&
  Fpos0 (upper zi) &&
  Fis0 (lower xi) &&
  Fis0 (upper xi).

Theorem rel_of_equal :
  forall a b : R, forall xi zi : FF,
  BND (a - b) xi ->
  rel_of_equal_helper xi zi = true ->
  REL a b zi.
Proof.
intros a b xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Fneg0_correct in H1.
apply Fpos0_correct in H2.
apply Fis0_correct in H3.
apply Fis0_correct in H4.
exists R0.
repeat split ; trivial.
rewrite Rplus_0_r, Rmult_1_r.
apply Rminus_diag_uniq.
unfold BND in Hx.
apply Rle_antisym.
now rewrite <- H4.
now rewrite <- H3.
Qed.

Lemma error_of_rel_generic :
 forall f,
 forall t: (forall x y : R, forall xi yi zi : FF,
            BND x xi -> BND y yi -> f xi yi zi = true ->
            BND (x * y) zi),
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 f xi yi zi = true ->
 BND (a - b) zi.
Proof.
intros f t a b xi yi zi (x,(Hr1,Hr2)).
cutrewrite (a - b = x * b)%R.
now apply t.
rewrite Hr2.
ring.
Qed.

Definition error_of_rel_pp := error_of_rel_generic mul_pp_helper mul_pp.
Definition error_of_rel_po := error_of_rel_generic mul_po_helper mul_po.
Definition error_of_rel_pn := error_of_rel_generic mul_pn_helper mul_pn.
Definition error_of_rel_op := error_of_rel_generic mul_op_helper mul_op.
Definition error_of_rel_oo := error_of_rel_generic mul_oo_helper mul_oo.
Definition error_of_rel_on := error_of_rel_generic mul_on_helper mul_on.
Definition error_of_rel_np := error_of_rel_generic mul_np_helper mul_np.
Definition error_of_rel_no := error_of_rel_generic mul_no_helper mul_no.
Definition error_of_rel_nn := error_of_rel_generic mul_nn_helper mul_nn.

Definition rel_subset_helper (xi zi : FF) :=
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem rel_subset :
  forall x xr : R, forall xi zi : FF,
  REL x xr xi ->
  rel_subset_helper xi zi = true ->
  REL x xr zi.
Proof.
intros x xr xi zi (xe,(Hx1,Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Fle2_correct in H1.
apply Fle2_correct in H2.
exists xe.
split.
apply IRsubset with (1 := H1) (2 := H2) (3 := Hx1).
exact Hx2.
Qed.

Definition intersect_rr_helper (xf yf : float2) (zi : FF) :=
  Fle2 (lower zi) (upper zi) &&
  Fle2 (lower zi) yf &&
  Fle2 xf (upper zi).

Theorem intersect_rr :
  forall z1 z2 : R, forall xi yi zi : FF,
  REL z1 z2 xi -> REL z1 z2 yi ->
  intersect_rr_helper (upper xi) (lower yi) zi = true ->
  REL z1 z2 zi.
Proof.
intros z1 z2 xi yi zi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Fle2_correct in H1.
apply Fle2_correct in H2.
apply Fle2_correct in H3.
case (Req_dec z2 0) ; intro.
exists (float2R (lower zi)).
split.
split.
apply Rle_refl.
exact H1.
rewrite Hx2.
rewrite H.
repeat rewrite Rmult_0_l.
apply refl_equal.
exists xe.
split.
split.
apply Rle_trans with (1 := H2).
replace xe with ye.
apply Hy1.
apply Rplus_eq_reg_l with R1.
apply Rmult_eq_reg_l with (2 := H).
now rewrite <- Hy2.
now apply Rle_trans with (2 := H3).
exact Hx2.
Qed.

Definition intersect_rr0_helper (xf yf : float2) (zi : FF) :=
  Flt2 xf yf &&
  Fneg0 (lower zi) &&
  Fpos0 (upper zi).

Theorem intersect_rr0 :
  forall z1 z2 : R, forall xi yi zi : FF,
  REL z1 z2 xi -> REL z1 z2 yi ->
  intersect_rr0_helper (upper xi) (lower yi) zi = true ->
  BND z2 zi.
Proof.
intros z1 z2 xi yi zi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Flt2_correct in H1.
apply Fneg0_correct in H2.
apply Fpos0_correct in H3.
destruct (Req_dec z2 0) as [Hz|Hz].
rewrite Hz.
now split.
elim (Rle_not_lt xe ye).
apply Req_le.
apply Rplus_eq_reg_l with R1.
apply Rmult_eq_reg_l with (2 := Hz).
now rewrite <- Hy2.
apply Rle_lt_trans with (1 := proj2 Hx1).
apply Rlt_le_trans with (2 := proj1 Hy1).
exact H1.
Qed.

Theorem absurd_intersect_rr :
  forall z1 z2 : R, forall xi yi : FF,
  REL z1 z2 xi -> REL z1 z2 yi -> NZR z2 ->
  Flt2 (upper xi) (lower yi) = true ->
  contradiction.
Proof.
intros z1 z2 xi yi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hz Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ (proj2 Hx1) H). clear H. intro H.
replace xe with ye in H.
generalize (Rlt_le_trans _ _ _ H (proj1 Hy1)). clear H. intro H.
elim (Rlt_irrefl _ H).
clear H.
apply sym_eq.
apply Rplus_eq_reg_l with R1.
apply Rmult_eq_reg_l with (2 := Hz).
now rewrite <- Hx2.
Qed.

Definition mul_rr_helper (xi yi zi : FF) :=
  Flt2_m1 (lower xi) &&
  Flt2_m1 (lower yi) &&
  Fle2 (lower zi) (Fplus2 (Fplus2 (lower xi) (lower yi))
                          (Fmult2 (lower xi) (lower yi))) &&
  Fle2 (Fplus2 (Fplus2 (upper xi) (upper yi))
               (Fmult2 (upper xi) (upper yi))) (upper zi).

Theorem mul_rr :
  forall x1 x2 y1 y2 : R, forall xi yi zi : FF,
  REL x1 x2 xi -> REL y1 y2 yi ->
  mul_rr_helper xi yi zi = true ->
  REL (x1 * y1) (x2 * y2) zi.
Proof.
intros x1 x2 y1 y2 xi yi zi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Flt2_m1_correct in H1.
apply Flt2_m1_correct in H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H4. intro H4.
exists (xe + ye + xe * ye)%R.
split.
apply IRcompose with (1 := Rlt_le _ _ H1) (2 := Rlt_le _ _ H2)
  (3 := H3) (4 := H4) (5 := Hx1) (6 := Hy1).
rewrite Hx2.
rewrite Hy2.
ring.
Qed.

Definition div_rr_helper (xi yi zi : FF) :=
  Flt2_m1 (lower xi) &&
  Flt2_m1 (lower yi) &&
  Fle2 (upper xi) (Fplus2 (Fplus2 (lower yi) (upper zi))
                          (Fmult2 (lower yi) (upper zi))) &&
  Fle2 (Fplus2 (Fplus2 (upper yi) (lower zi))
               (Fmult2 (upper yi) (lower zi))) (lower xi).

Theorem div_rr :
  forall x1 x2 y1 y2 : R, forall xi yi zi : FF,
  REL x1 x2 xi -> REL y1 y2 yi -> NZR y2 ->
  div_rr_helper xi yi zi = true ->
  REL (x1 / y1) (x2 / y2) zi.
Proof.
intros x1 x2 y1 y2 xi yi zi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hy4 Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Flt2_m1_correct in H1.
apply Flt2_m1_correct in H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H4. intro H4.
exists ((xe - ye) / (1 + ye))%R.
split.
apply IRcompose_inv with (1 := Rlt_le _ _ H1) (2 := H2)
 (3 := H4) (4 := H3) (5 := Hx1) (6 := Hy1).
rewrite Hx2.
rewrite Hy2.
field.
split.
apply Rgt_not_eq.
apply Rlt_le_trans with (2 := Rplus_le_compat_l R1 _ _ (proj1 Hy1)).
rewrite <- (Rplus_opp_r 1).
apply Rplus_lt_compat_l with (1 := H2).
exact Hy4.
Qed.

Theorem compose :
  forall x1 x2 y2 : R, forall xi yi zi : FF,
  REL x1 x2 xi -> REL x2 y2 yi ->
  mul_rr_helper xi yi zi = true ->
  REL x1 y2 zi.
Proof.
intros x1 x2 y2 xi yi zi Hx Hy Hb.
generalize (mul_rr _ _ _ _ _ _ _ Hx Hy Hb).
destruct Hx as (xe,(Hx1,Hx2)).
destruct Hy as (ye,(Hy1,Hy2)).
intros (ze,(Hz1,Hz2)).
exists ze.
split.
exact Hz1.
case (Req_dec y2 0) ; intro.
rewrite Hx2.
rewrite Hy2.
rewrite H.
repeat rewrite Rmult_0_l.
apply refl_equal.
apply Rmult_eq_reg_l with x2.
rewrite Rmult_comm.
now rewrite <- Rmult_assoc.
rewrite Hy2.
apply prod_neq_R0.
exact H.
apply Rgt_not_eq.
rewrite <- (Rplus_opp_r R1).
unfold Rgt.
apply Rplus_lt_compat_l.
apply Rlt_le_trans with (2 := proj1 Hy1).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,_).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,_).
generalize (andb_prop _ _ Hb). clear Hb. intros (_,H0).
now apply Flt2_m1_correct.
Qed.

End Gappa_pred_rel.
