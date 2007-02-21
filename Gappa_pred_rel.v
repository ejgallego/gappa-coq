Require Import Gappa_common.

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

Theorem rel_of_nzr_bnd :
 forall a b : R, forall zi : FF,
 NZR b -> BND ((a - b) / b) zi ->
 Flt2 (Float2 (-1) 0) (lower zi) = true ->
 REL a b zi.
intros a b zi Hb Hr H.
generalize (Flt2_correct _ _ H).
cutrewrite (Float2 (-1) 0 = -1 :>R)%R.
2: unfold float2R ; auto with real.
clear H. intro H.
exists ((a - b) / b)%R.
split.
exact H.
split.
exact Hr.
field.
exact Hb.
Qed.

Definition error_of_rel_pp_helper (xi yi zi : FF) :=
 Fpos0 (lower xi) &&
 Fpos (lower yi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (lower yi)) &&
 Fle2 (Fmult2 (upper xi) (upper yi)) (upper zi).

Theorem error_of_rel_pp :
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 error_of_rel_pp_helper xi yi zi = true ->
 BND (a - b) zi.
intros a b xi yi zi Hr Hb H.
generalize (andb_prop _ _ H). clear H. intros (H,H4).
generalize (andb_prop _ _ H). clear H. intros (H,H3).
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
assert (b <> 0)%R.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
cutrewrite (a - b = (a - b) / b * b)%R.
unfold BND.
apply IRmult_pp with (1 := H1) (2 := Rlt_le _ _ H2) (3 := H3) (4 := H4) (6 := Hb).
apply bnd_of_nzr_rel.
exact H.
exact Hr.
field.
exact H.
Qed.

Definition error_of_rel_pn_helper (xi yi zi : FF) :=
 Fpos0 (lower xi) &&
 Fneg (upper yi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (lower yi)) &&
 Fle2 (Fmult2 (lower xi) (upper yi)) (upper zi).

Theorem error_of_rel_pn :
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 error_of_rel_pn_helper xi yi zi = true ->
 BND (a - b) zi.
intros a b xi yi zi Hr Hb H.
generalize (andb_prop _ _ H). clear H. intros (H,H4).
generalize (andb_prop _ _ H). clear H. intros (H,H3).
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fneg_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
assert (b <> 0)%R.
apply Rlt_not_eq.
apply Rle_lt_trans with (1 := proj2 Hb) (2 := H2).
cutrewrite (a - b = (a - b) / b * b)%R.
unfold BND.
apply IRmult_pn with (1 := H1) (2 := Rlt_le _ _ H2) (3 := H3) (4 := H4) (6 := Hb).
apply bnd_of_nzr_rel.
exact H.
exact Hr.
field.
exact H.
Qed.

Definition error_of_rel_np_helper (xi yi zi : FF) :=
 Fneg0 (upper xi) &&
 Fpos (lower yi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (upper yi)) &&
 Fle2 (Fmult2 (upper xi) (lower yi)) (upper zi).

Theorem error_of_rel_np :
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 error_of_rel_np_helper xi yi zi = true ->
 BND (a - b) zi.
intros a b xi yi zi Hr Hb H.
generalize (andb_prop _ _ H). clear H. intros (H,H4).
generalize (andb_prop _ _ H). clear H. intros (H,H3).
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
assert (b <> 0)%R.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
cutrewrite (a - b = (a - b) / b * b)%R.
unfold BND.
apply IRmult_np with (1 := H1) (2 := Rlt_le _ _ H2) (3 := H3) (4 := H4) (6 := Hb).
apply bnd_of_nzr_rel.
exact H.
exact Hr.
field.
exact H.
Qed.

Definition error_of_rel_nn_helper (xi yi zi : FF) :=
 Fneg0 (upper xi) &&
 Fneg (upper yi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (upper yi)) &&
 Fle2 (Fmult2 (lower xi) (lower yi)) (upper zi).

Theorem error_of_rel_nn :
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 error_of_rel_nn_helper xi yi zi = true ->
 BND (a - b) zi.
intros a b xi yi zi Hr Hb H.
generalize (andb_prop _ _ H). clear H. intros (H,H4).
generalize (andb_prop _ _ H). clear H. intros (H,H3).
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fneg_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
assert (b <> 0)%R.
apply Rlt_not_eq.
apply Rle_lt_trans with (1 := proj2 Hb) (2 := H2).
cutrewrite (a - b = (a - b) / b * b)%R.
unfold BND.
apply IRmult_nn with (1 := H1) (2 := Rlt_le _ _ H2) (3 := H3) (4 := H4) (6 := Hb).
apply bnd_of_nzr_rel.
exact H.
exact Hr.
field.
exact H.
Qed.

Definition error_of_rel_op_helper (xi yi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fpos (lower yi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (upper yi)) &&
 Fle2 (Fmult2 (upper xi) (upper yi)) (upper zi).

Theorem error_of_rel_op :
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 error_of_rel_op_helper xi yi zi = true ->
 BND (a - b) zi.
intros a b xi yi zi Hr Hb H.
generalize (andb_prop _ _ H). clear H. intros (H,H5).
generalize (andb_prop _ _ H). clear H. intros (H,H4).
generalize (andb_prop _ _ H). clear H. intros (H,H3).
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fpos_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
assert (b <> 0)%R.
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H3) (2 := proj1 Hb).
cutrewrite (a - b = (a - b) / b * b)%R.
unfold BND.
apply IRmult_op with (1 := H1) (2 := H2) (3 := Rlt_le _ _ H3) (4 := H4) (5 := H5) (7 := Hb).
apply bnd_of_nzr_rel.
exact H.
exact Hr.
field.
exact H.
Qed.

Definition error_of_rel_on_helper (xi yi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg (upper yi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (lower yi)) &&
 Fle2 (Fmult2 (lower xi) (lower yi)) (upper zi).

Theorem error_of_rel_on :
 forall a b : R, forall xi yi zi : FF,
 REL a b xi -> BND b yi ->
 error_of_rel_on_helper xi yi zi = true ->
 BND (a - b) zi.
intros a b xi yi zi Hr Hb H.
generalize (andb_prop _ _ H). clear H. intros (H,H5).
generalize (andb_prop _ _ H). clear H. intros (H,H4).
generalize (andb_prop _ _ H). clear H. intros (H,H3).
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fneg_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
assert (b <> 0)%R.
apply Rlt_not_eq.
apply Rle_lt_trans with (1 := proj2 Hb) (2 := H3).
cutrewrite (a - b = (a - b) / b * b)%R.
unfold BND.
apply IRmult_on with (1 := H1) (2 := H2) (3 := Rlt_le _ _ H3) (4 := H4) (5 := H5) (7 := Hb).
apply bnd_of_nzr_rel.
exact H.
exact Hr.
field.
exact H.
Qed.

Definition mul_rr_helper (xi yi zi : FF) :=
 Flt2 (Float2 (-1) 0) (lower zi) &&
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
generalize (Flt2_correct _ _ H1).
cutrewrite (Float2 (-1) 0 = -1 :>R)%R.
2: unfold float2R ; auto with real.
clear H1. intro H1.
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

End Gappa_pred_rel.