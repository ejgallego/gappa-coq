Require Import Gappa_common.
Require Import Gappa_pred_bnd.

Theorem bnd_of_nzr_rel :
 forall a b : R, forall zi : FF,
 NZR b -> REL a b zi ->
 BND ((a - b) / b) zi.
Proof.
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

Definition one_plus (xi : FF) :=
  makepairF (Fplus2 (Float2 1 0) (lower xi)) (Fplus2 (Float2 1 0) (upper xi)).

Lemma one_plus_correct :
  forall x xi,
  BND x xi ->
  BND (1 + x) (one_plus xi).
Proof.
intros x xi Hx.
apply IRplus with (xl := 1%R) (xu := 1%R) (4 := Hx) ; simpl.
rewrite Fplus2_correct.
apply Rplus_le_compat_r.
unfold float2R, Defs.F2R. simpl.
rewrite Rmult_1_l.
apply Rle_refl.
rewrite Fplus2_correct.
apply Rplus_le_compat_r.
unfold float2R, Defs.F2R. simpl.
rewrite Rmult_1_l.
apply Rle_refl.
split ; apply Rle_refl.
Qed.

Theorem bnd_of_bnd_rel_p :
  forall x y : R, forall yi ei xi : FF,
  BND y yi -> REL x y ei ->
  mul_pp_helper yi (one_plus ei) xi = true ->
  BND x xi.
Proof.
intros x y yi ei xi Hy (e,(He1,He2)) Hb.
rewrite He2.
apply mul_pp with (1 := Hy) (3 := Hb).
apply one_plus_correct with (1 := He1).
Qed.

Theorem bnd_of_bnd_rel_o :
  forall x y : R, forall yi ei xi : FF,
  BND y yi -> REL x y ei ->
  mul_op_helper yi (one_plus ei) xi = true ->
  BND x xi.
Proof.
intros x y yi ei xi Hy (e,(He1,He2)) Hb.
rewrite He2.
apply mul_op with (1 := Hy) (3 := Hb).
apply one_plus_correct with (1 := He1).
Qed.

Theorem bnd_of_bnd_rel_n :
  forall x y : R, forall yi ei xi : FF,
  BND y yi -> REL x y ei ->
  mul_np_helper yi (one_plus ei) xi = true ->
  BND x xi.
Proof.
intros x y yi ei xi Hy (e,(He1,He2)) Hb.
rewrite He2.
apply mul_np with (1 := Hy) (3 := Hb).
apply one_plus_correct with (1 := He1).
Qed.

Lemma rel_swap :
  forall x y e ei,
  BND e ei ->
  x = (y * (1 + e))%R ->
  Fpos (lower (one_plus ei)) = true ->
  y = (x / (1 + e))%R.
Proof.
intros x y e ei He Hx Hb.
rewrite Hx.
field.
apply Rgt_not_eq.
apply Rlt_gt.
assert (H := one_plus_correct _ _ He).
destruct H as (H,_).
apply Rlt_le_trans with (2 := H).
now apply Fpos_correct.
Qed.

Theorem bnd_of_rel_bnd_p :
  forall x y : R, forall xi ei yi : FF,
  BND x xi -> REL x y ei ->
  div_pp_helper xi (one_plus ei) yi = true ->
  BND y yi.
Proof.
intros x y yi ei xi Hy (e,(He1,He2)) Hb.
destruct (andb_prop _ _ Hb) as (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
rewrite rel_swap with (1 := He1) (2 := He2) (3 := H1).
apply div_pp with (1 := Hy) (3 := Hb).
apply one_plus_correct with (1 := He1).
Qed.

Theorem bnd_of_rel_bnd_o :
  forall x y : R, forall xi ei yi : FF,
  BND x xi -> REL x y ei ->
  div_op_helper xi (one_plus ei) yi = true ->
  BND y yi.
Proof.
intros x y yi ei xi Hy (e,(He1,He2)) Hb.
destruct (andb_prop _ _ Hb) as (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
rewrite rel_swap with (1 := He1) (2 := He2) (3 := H1).
apply div_op with (1 := Hy) (3 := Hb).
apply one_plus_correct with (1 := He1).
Qed.

Theorem bnd_of_rel_bnd_n :
  forall x y : R, forall xi ei yi : FF,
  BND x xi -> REL x y ei ->
  div_np_helper xi (one_plus ei) yi = true ->
  BND y yi.
Proof.
intros x y yi ei xi Hy (e,(He1,He2)) Hb.
destruct (andb_prop _ _ Hb) as (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
generalize (andb_prop _ _ H1). clear H1. intros (H1,_).
rewrite rel_swap with (1 := He1) (2 := He2) (3 := H1).
apply div_np with (1 := Hy) (3 := Hb).
apply one_plus_correct with (1 := He1).
Qed.

Theorem rel_refl :
  forall a : R, forall zi : FF,
  contains_zero_helper zi = true ->
  REL a a zi.
Proof.
intros a zi Hb.
exists R0.
split.
now apply contains_zero.
ring.
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
apply Rplus_eq_reg_l with 1%R.
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
apply Rplus_eq_reg_l with 1%R.
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
  False.
Proof.
intros z1 z2 xi yi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hz Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ (proj2 Hx1) H). clear H. intro H.
replace xe with ye in H.
generalize (Rlt_le_trans _ _ _ H (proj1 Hy1)). clear H. intro H.
elim (Rlt_irrefl _ H).
clear H.
apply sym_eq.
apply Rplus_eq_reg_l with 1%R.
apply Rmult_eq_reg_l with (2 := Hz).
now rewrite <- Hx2.
Qed.

Definition mul_rr_helper (xi yi zi : FF) :=
  Fle2_m1 (lower xi) &&
  Fle2_m1 (lower yi) &&
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
apply Fle2_m1_correct in H1.
apply Fle2_m1_correct in H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H4. intro H4.
exists (xe + ye + xe * ye)%R.
split.
apply IRcompose with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := Hx1) (6 := Hy1).
rewrite Hx2.
rewrite Hy2.
ring.
Qed.

Definition div_rr_helper (xi yi zi : FF) :=
  Fle2_m1 (lower xi) &&
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
apply Fle2_m1_correct in H1.
apply Flt2_m1_correct in H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H4. intro H4.
exists ((xe - ye) / (1 + ye))%R.
split.
apply IRcompose_inv with (1 := H1) (2 := H2) (3 := H4) (4 := H3) (5 := Hx1) (6 := Hy1).
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

Definition inv_r_helper (xi zi : FF) :=
  Flt2_m1 (lower xi) &&
  Fpos0 (Fplus2 (Fplus2 (lower xi) (upper zi)) (Fmult2 (lower xi) (upper zi))) &&
  Fneg0 (Fplus2 (Fplus2 (upper xi) (lower zi)) (Fmult2 (upper xi) (lower zi))).

Theorem inv_r :
  forall x1 x2 y : R, forall xi zi : FF,
  REL x1 x2 xi -> NZR x2 ->
  inv_r_helper xi zi = true ->
  REL (y / x1) (y / x2) zi.
Proof.
intros x1 x2 y xi zi (xe,(Hx1,Hx2)) Hx3 Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Flt2_m1_correct in H1.
generalize (Fpos0_correct _ H2).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H2. intro H2.
generalize (Fneg0_correct _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
exists ((0 - xe) / (1 + xe))%R.
split.
apply IRcompose_inv with (xl := R0) (xu := R0) (2 := H1) (3 := H3) (4 := H2) (6 := Hx1).
apply Rge_le, Ropp_0_le_ge_contravar, Rle_0_1.
split ; apply Rle_refl.
rewrite Hx2.
field.
split.
apply Rgt_not_eq.
apply Rlt_le_trans with (2 := Rplus_le_compat_l R1 _ _ (proj1 Hx1)).
rewrite <- (Rplus_opp_r 1).
apply Rplus_lt_compat_l with (1 := H1).
exact Hx3.
Qed.

Theorem compose :
  forall x1 x2 y2 : R, forall xi yi zi : FF,
  REL x1 x2 xi -> REL x2 y2 yi ->
  mul_rr_helper xi yi zi = true ->
  REL x1 y2 zi.
Proof.
intros x1 x2 y2 xi yi zi (xe,(Hx1,Hx2)) (ye,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply Fle2_m1_correct in H1.
apply Fle2_m1_correct in H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H4. intro H4.
exists (xe + ye + xe * ye)%R.
split.
apply IRcompose with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := Hx1) (6 := Hy1).
rewrite Hx2.
rewrite Hy2.
ring.
Qed.

Theorem compose_swap :
  forall x y r1 r2 : R, forall xi yi zi : FF,
  REL x (y * r2) xi -> REL r1 (1 / r2) yi -> NZR r2 ->
  mul_rr_helper xi yi zi = true ->
  REL (x * r1) y zi.
Proof.
intros x y r1 r2 xi yi zi Hx Hy Hr Hb.
generalize (mul_rr _ _ _ _ _ _ _ Hx Hy Hb).
replace (y * r2 * (1 / r2))%R with y.
easy.
now field.
Qed.

Definition FImult2 (x : float2) (yi : FF) :=
  let (yl,yu) := yi in
  if Fpos0 x then makepairF (Fmult2 x yl) (Fmult2 x yu)
  else makepairF (Fmult2 x yu) (Fmult2 x yl).

Lemma FImult2_correct :
  forall (x : float2) yi y, BND y yi ->
  BND (x * y) (FImult2 x yi).
Proof.
intros x (yl,yu) y Hy.
unfold FImult2.
replace (Fpos0 x) with (Zle_bool 0 (Fnum x)) by now unfold Fpos0 ; case (Fnum x).
case Zle_bool_spec ; split ; simpl ; rewrite Fmult2_correct.
apply monotony_1p.
now apply Float_prop.F2R_ge_0.
apply Hy.
apply monotony_1p.
now apply Float_prop.F2R_ge_0.
apply Hy.
apply monotony_1n.
apply Float_prop.F2R_le_0.
now apply Zlt_le_weak.
apply Hy.
apply monotony_1n.
apply Float_prop.F2R_le_0.
now apply Zlt_le_weak.
apply Hy.
Qed.

Definition add_rr_helper (xi yi qi zi : FF) :=
  let xql := FImult2 (lower qi) xi in
  let xqu := FImult2 (upper qi) xi in
  let yql := FImult2 (Fminus2 (Float2 1 0) (lower qi)) yi in
  let yqu := FImult2 (Fminus2 (Float2 1 0) (upper qi)) yi in
  Fle2 (lower zi) (Fplus2 (lower xql) (lower yql)) &&
  Fle2 (lower zi) (Fplus2 (lower xqu) (lower yqu)) &&
  Fle2 (Fplus2 (upper xql) (upper yql)) (upper zi) &&
  Fle2 (Fplus2 (upper xqu) (upper yqu)) (upper zi).

Theorem add_rr :
  forall x1 x2 y1 y2 : R, forall xi yi qi zi : FF,
  REL x1 x2 xi -> REL y1 y2 yi -> BND (x2 / (x2 + y2)) qi -> NZR (x2 + y2) ->
  add_rr_helper xi yi qi zi = true ->
  REL (x1 + y1) (x2 + y2) zi.
Proof.
intros x1 x2 y1 y2 xi yi qi zi (ex,(Hx1,Hx2)) (ey,(Hy1,Hy2)) Hq Zxy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb, H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb, H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1, H2).
apply Fle2_correct in H1. rewrite Fplus2_correct in H1.
apply Fle2_correct in H2. rewrite Fplus2_correct in H2.
apply Fle2_correct in H3. rewrite Fplus2_correct in H3.
apply Fle2_correct in H4. rewrite Fplus2_correct in H4.
assert (H5 := FImult2_correct (lower qi) xi _ Hx1).
assert (H6 := FImult2_correct (upper qi) xi _ Hx1).
assert (H7 := FImult2_correct (Fminus2 (Float2 1 0) (lower qi)) yi _ Hy1).
assert (H8 := FImult2_correct (Fminus2 (Float2 1 0) (upper qi)) yi _ Hy1).
assert (H9 : float2R (Float2 1 0) = R1) by apply Rmult_1_r.
assert (Ha : (float2R (Fminus2 (Float2 1 0) (lower qi)) = 1 - lower qi)%R).
now rewrite Fminus2_correct, H9.
assert (Hb : (float2R (Fminus2 (Float2 1 0) (upper qi)) = 1 - upper qi)%R).
now rewrite Fminus2_correct, H9.
exists ((x1 + y1) / (x2 + y2) - 1)%R.
split.
2: now field.
rewrite Hx2, Hy2.
replace ((x2 * (1 + ex) + y2 * (1 + ey)) / (x2 + y2) - 1)%R with
  (ey + x2 / (x2 + y2) * (ex - ey))%R by now field.
unfold BND in Hq.
destruct (Rle_or_lt (ex - ey) 0) as [He|He].
split.
apply Rle_trans with (ey + upper qi * (ex - ey))%R.
replace (ey + upper qi * (ex - ey))%R with (upper qi * ex + (1 - upper qi) * ey)%R by ring.
apply Rle_trans with (1 := H2).
apply Rplus_le_compat.
apply H6.
rewrite <- Hb.
apply H8.
apply Rplus_le_compat_l.
now apply monotony_2n.
apply Rle_trans with (ey + lower qi * (ex - ey))%R.
apply Rplus_le_compat_l.
now apply monotony_2n.
replace (ey + lower qi * (ex - ey))%R with (lower qi * ex + (1 - lower qi) * ey)%R by ring.
apply Rle_trans with (2 := H3).
apply Rplus_le_compat.
apply H5.
rewrite <- Ha.
apply H7.
apply Rlt_le in He.
split.
apply Rle_trans with (ey + lower qi * (ex - ey))%R.
replace (ey + lower qi * (ex - ey))%R with (lower qi * ex + (1 - lower qi) * ey)%R by ring.
apply Rle_trans with (1 := H1).
apply Rplus_le_compat.
apply H5.
rewrite <- Ha.
apply H7.
apply Rplus_le_compat_l.
now apply monotony_2p.
apply Rle_trans with (ey + upper qi * (ex - ey))%R.
apply Rplus_le_compat_l.
now apply monotony_2p.
replace (ey + upper qi * (ex - ey))%R with (upper qi * ex + (1 - upper qi) * ey)%R by ring.
apply Rle_trans with (2 := H4).
apply Rplus_le_compat.
apply H6.
rewrite <- Hb.
apply H8.
Qed.

Theorem sub_rr :
  forall x1 x2 y1 y2 : R, forall xi yi qi zi : FF,
  REL x1 x2 xi -> REL y1 y2 yi -> BND (x2 / (x2 - y2)) qi -> NZR (x2 - y2) ->
  add_rr_helper xi yi qi zi = true ->
  REL (x1 - y1) (x2 - y2) zi.
Proof.
intros x1 x2 y1 y2 xi yi qi zi Hx (ey,(Hy1,Hy2)) Hq Zxy Hb.
apply add_rr with (1 := Hx) (3 := Hq) (4 := Zxy) (5 := Hb).
exists ey.
split.
exact Hy1.
rewrite Hy2.
ring.
Qed.

Definition mul_helper (xi yi zi : FF) :=
  let xly := FImult2 (lower xi) yi in
  let xuy := FImult2 (upper xi) yi in
  Fle2 (lower zi) (lower xly) &&
  Fle2 (lower zi) (lower xuy) &&
  Fle2 (upper xly) (upper zi) &&
  Fle2 (upper xuy) (upper zi).

Theorem bnd_div_of_rel_bnd_div :
  forall x1 x2 y : R, forall xi yi zi : FF,
  REL x1 x2 xi -> BND (x2 / y) yi -> NZR y ->
  mul_helper xi yi zi = true ->
  BND ((x1 - x2) / y) zi.
Proof.
intros x1 x2 y xi yi zi (ex,(Hx1,Hx2)) Hxy Zy Hb.
rewrite Hx2.
replace ((x2 * (1 + ex) - x2) / y)%R with (ex * (x2 / y))%R by now field.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb, H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb, H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1, H2).
apply Fle2_correct in H1.
apply Fle2_correct in H2.
apply Fle2_correct in H3.
apply Fle2_correct in H4.
assert (H5 := FImult2_correct (lower xi) yi _ Hxy).
assert (H6 := FImult2_correct (upper xi) yi _ Hxy).
destruct (Rle_or_lt 0 (x2 / y)) as [Hy|Hy].
split.
apply Rle_trans with (1 := H1).
apply Rle_trans with (1 := proj1 H5).
now apply monotony_2p.
apply Rle_trans with (2 := H4).
apply Rle_trans with (2 := proj2 H6).
now apply monotony_2p.
apply Rlt_le in Hy.
split.
apply Rle_trans with (1 := H2).
apply Rle_trans with (1 := proj1 H6).
now apply monotony_2n.
apply Rle_trans with (2 := H3).
apply Rle_trans with (2 := proj2 H5).
now apply monotony_2n.
Qed.
