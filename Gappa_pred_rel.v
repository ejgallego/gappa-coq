Require Import Gappa_common.
Require Import Gappa_pred_bnd.

Section Gappa_pred_rel.

Theorem bnd_of_nzr_rel :
 forall a b : R, forall zi : FF,
 NZR b -> REL a b zi ->
 BND ((a - b) / b) zi.
intros a b zi Hb (x,(_,(Hr1,Hr2))).
cutrewrite ((a - b) / b = x)%R.
exact Hr1.
rewrite Hr2.
field.
exact Hb.
Qed.

Definition Flt2_m1 f :=
 Flt2 (Float2 (-1) 0) f.

Lemma Flt2_m1_correct :
 forall f,
 Flt2_m1 f = true ->
 (-1 < f)%R.
intros f Hb.
exact (Flt2_correct _ _ Hb).
Qed.

Theorem rel_of_nzr_bnd :
 forall a b : R, forall zi : FF,
 NZR b -> BND ((a - b) / b) zi ->
 Flt2_m1 (lower zi) = true ->
 REL a b zi.
intros a b zi Hb Hr H.
generalize (Flt2_m1_correct _ H). clear H. intro H.
exists ((a - b) / b)%R.
split.
exact H.
split.
exact Hr.
field.
exact Hb.
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
intros f t a b xi yi zi (x,(_,(Hr1,Hr2))).
cutrewrite (a - b = x * b)%R.
apply t.
exact Hr1.
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
 Flt2_m1 (lower zi) &&
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem rel_subset :
 forall x xr : R, forall xi zi : FF,
 REL x xr xi ->
 rel_subset_helper xi zi = true ->
 REL x xr zi.
intros x xr xi zi (xe,(Hx1,(Hx2,Hx3))) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_m1_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
exists xe.
split.
exact H1.
split.
apply IRsubset with (1 := H2) (2 := H3) (3 := Hx2).
exact Hx3.
Qed.

Definition intersect_rr_helper (xf yf : float2) (zi : FF) :=
 Flt2_m1 (lower zi) &&
 Fle2 (lower zi) (upper zi) &&
 Fle2 (lower zi) yf &&
 Fle2 xf (upper zi).

Theorem intersect_rr :
 forall z1 z2 : R, forall xi yi zi : FF,
 REL z1 z2 xi -> REL z1 z2 yi ->
 intersect_rr_helper (upper xi) (lower yi) zi = true ->
 REL z1 z2 zi.
intros z1 z2 xi yi zi (xe,(Hx1,(Hx2,Hx3))) (ye,(Hy1,(Hy2,Hy3))) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_m1_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). clear H4. intro H4.
case (Req_dec z2 0) ; intro.
exists (float2R (lower zi)).
split.
exact H1.
split.
split.
apply Rle_refl.
exact H2.
rewrite Hx3.
rewrite H.
repeat rewrite Rmult_0_l.
apply refl_equal.
exists xe.
split.
exact H1.
split.
split.
apply Rle_trans with (1 := H3).
replace xe with ye.
exact (proj1 Hy2).
apply Rplus_eq_reg_l with R1.
apply Rmult_eq_reg_l with (2 := H).
rewrite <- Hy3.
exact Hx3.
apply Rle_trans with (2 := H4).
exact (proj2 Hx2).
exact Hx3.
Qed.

Theorem absurd_intersect_rr :
 forall z1 z2 : R, forall xi yi : FF,
 REL z1 z2 xi -> REL z1 z2 yi -> NZR z2 ->
 Flt2 (upper xi) (lower yi) = true ->
 contradiction.
intros z1 z2 xi yi (xe,(Hx1,(Hx2,Hx3))) (ye,(Hy1,(Hy2,Hy3))) Hz Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ (proj2 Hx2) H). clear H. intro H.
replace xe with ye in H.
generalize (Rlt_le_trans _ _ _ H (proj1 Hy2)). clear H. intro H.
elim (Rlt_irrefl _ H).
clear H.
apply sym_eq.
apply Rplus_eq_reg_l with R1.
apply Rmult_eq_reg_l with (2 := Hz).
rewrite <- Hx3.
exact Hy3.
Qed.

Definition mul_rr_helper (xi yi zi : FF) :=
 Flt2_m1 (lower zi) &&
 Fle2 (lower zi) (Fplus2 (Fplus2 (lower xi) (lower yi))
                         (Fmult2 (lower xi) (lower yi))) &&
 Fle2 (Fplus2 (Fplus2 (upper xi) (upper yi))
              (Fmult2 (upper xi) (upper yi))) (upper zi).

Theorem mul_rr :
 forall x1 x2 y1 y2 : R, forall xi yi zi : FF,
 REL x1 x2 xi -> REL y1 y2 yi ->
 mul_rr_helper xi yi zi = true ->
 REL (x1 * y1) (x2 * y2) zi.
intros x1 x2 y1 y2 xi yi zi (xe,(Hx1,(Hx2,Hx3))) (ye,(Hy1,(Hy2,Hy3))) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_m1_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
exists (xe + ye + xe * ye)%R.
split.
exact H1.
split.
apply IRcompose with (1 := Rlt_le _ _ Hx1) (2 := Rlt_le _ _ Hy1)
 (3 := H2) (4 := H3) (5 := Hx2) (6 := Hy2).
rewrite Hx3.
rewrite Hy3.
ring.
Qed.

Definition div_rr_helper (xi yi zi : FF) :=
 Flt2_m1 (lower zi) &&
 Fle2 (upper xi) (Fplus2 (Fplus2 (lower yi) (upper zi))
                         (Fmult2 (lower yi) (upper zi))) &&
 Fle2 (Fplus2 (Fplus2 (upper yi) (lower zi))
              (Fmult2 (upper yi) (lower zi))) (lower xi).

Theorem div_rr :
 forall x1 x2 y1 y2 : R, forall xi yi zi : FF,
 REL x1 x2 xi -> REL y1 y2 yi -> NZR y2 ->
 div_rr_helper xi yi zi = true ->
 REL (x1 / y1) (x2 / y2) zi.
intros x1 x2 y1 y2 xi yi zi (xe,(Hx1,(Hx2,Hx3))) (ye,(Hy1,(Hy2,Hy3))) Hy4 Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_m1_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
exists ((xe - ye) / (1 + ye))%R.
split.
exact H1.
split.
apply IRcompose_inv with (1 := Rlt_le _ _ Hx1) (2 := Hy1)
 (3 := H3) (4 := H2) (5 := Hx2) (6 := Hy2).
rewrite Hx3.
rewrite Hy3.
field.
split.
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (2 := Rplus_le_compat_l R1 _ _ (proj1 Hy2)).
replace R0 with (1 + -1)%R. 2: ring.
apply Rplus_lt_compat_l with (1 := Hy1).
exact Hy4.
Qed.

Theorem compose :
 forall x1 x2 y2 : R, forall xi yi zi : FF,
 REL x1 x2 xi -> REL x2 y2 yi ->
 mul_rr_helper xi yi zi = true ->
 REL x1 y2 zi.
intros x1 x2 y2 xi yi zi Hx Hy Hb.
generalize (mul_rr _ _ _ _ _ _ _ Hx Hy Hb).
destruct Hx as (xe,(Hx1,(Hx2,Hx3))).
destruct Hy as (ye,(Hy1,(Hy2,Hy3))).
intros (ze,(Hz1,(Hz2,Hz3))).
exists ze.
split.
exact Hz1.
split.
exact Hz2.
case (Req_dec y2 0) ; intro.
rewrite Hx3.
rewrite Hy3.
rewrite H.
repeat rewrite Rmult_0_l.
apply refl_equal.
apply Rmult_eq_reg_l with x2.
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
exact Hz3.
rewrite Hy3.
apply prod_neq_R0.
exact H.
apply Rgt_not_eq.
rewrite <- (Rplus_opp_r R1).
apply Rplus_gt_compat_l.
apply Rge_gt_trans with (1 := Rle_ge _ _ (proj1 Hy2)).
exact Hy1.
Qed.

End Gappa_pred_rel.
