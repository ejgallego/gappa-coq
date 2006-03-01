Require Import AllFloat.
Require Import Gappa_common.

Section Gappa_pred_abs.

Axiom Rabs_def2b :
 forall x a : R, (Rabs x <= a)%R -> (-a <= x <= a)%R.

Definition bnd_of_abs_helper (xi zi : FF) :=
 Fle2 (lower zi) (Fopp (upper xi)) &&
 Fle2 (upper xi) (upper zi).

Theorem bnd_of_abs :
 forall x : R, forall xi zi : FF,
 ABS x xi ->
 bnd_of_abs_helper xi zi = true ->
 BND x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). unfold float2R. rewrite Fopp_correct. fold float2R. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
assert (H : (-(upper xi) <= x <= (upper xi))%R).
apply (Rabs_def2b _ _ (proj2 (proj2 Hx))).
split.
apply Rle_trans with (1 := H1) (2 := proj1 H).
apply Rle_trans with (1 := proj2 H) (2 := H2).
Qed.

Definition abs_of_bnd_helper (xi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem abs_of_bnd :
 forall x : R, forall xi zi : FF,
 BND (Rabs x) xi ->
 abs_of_bnd_helper xi zi = true ->
 ABS x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
unfold ABS.
split.
exact H1.
split.
apply Rle_trans with (1 := H2) (2 := proj1 Hx).
apply Rle_trans with (1 := proj2 Hx) (2 := H3).
Qed.

Definition mul_aa_helper (xi yi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (Fmult (lower xi) (lower yi)) &&
 Fle2 (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_aa :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 mul_aa_helper xi yi zi = true ->
 ABS (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fmult_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
unfold ABS, bndR in *.
split.
exact H1.
rewrite Rabs_mult.
apply ImultR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; intuition.
Qed.

Definition div_aa_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fpos0 (lower zi) &&
 Fle2 (Fmult (upper yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult (lower yi) (upper zi)).

Theorem div_aa :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 div_aa_helper xi yi zi = true ->
 ABS (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H2).
generalize (Fpos_correct _ Hb). intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
split.
exact H2.
replace (Rabs (x / y)) with (Rabs x / Rabs y)%R.
unfold ABS, bndR in *.
apply IdivR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; intuition.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rabs_Rinv.
apply refl_equal.
apply abs_not_zero_correct with (1 := Hy) (2 := Hb).
Qed.

Definition add_aa_p_helper (xi yi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (Fminus2 (lower xi) (upper yi)) &&
 Fle2 (Fplus2 (upper xi) (upper yi)) (upper zi).

Theorem add_aa_p :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 add_aa_p_helper xi yi zi = true ->
 ABS (x + y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fminus2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fplus2_correct. clear H3. intro H3.
split.
exact H1.
split.
apply Rle_trans with (Rabs x - Rabs y)%R.
apply Rle_trans with (1 := H2).
unfold Rminus.
apply Rplus_le_compat with (1 := proj1 (proj2 Hx)).
apply Ropp_le_contravar with (1 := proj2 (proj2 Hy)).
replace (x + y)%R with (x - -y)%R. 2: ring.
rewrite<- (Rabs_Ropp y).
apply Rabs_triang_inv.
apply Rle_trans with (Rabs x + Rabs y)%R.
apply Rabs_triang.
apply Rle_trans with (2 := H3).
apply Rplus_le_compat with (1 := proj2 (proj2 Hx)) (2 := proj2 (proj2 Hy)).
Qed.

Definition add_aa_o_helper (xi yi zi : FF) :=
 Fis0 (lower zi) &&
 Fle2 (Fplus2 (upper xi) (upper yi)) (upper zi).

Theorem add_aa_o :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 add_aa_o_helper xi yi zi = true ->
 ABS (x + y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fis0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fplus2_correct. clear H2. intro H2.
split.
auto with real.
split.
replace (Gappa_real.lower zi) with (float2R (lower zi)). 2: trivial.
rewrite H1.
apply Rabs_pos.
apply Rle_trans with (Rabs x + Rabs y)%R.
apply Rabs_triang.
apply Rle_trans with (2 := H2).
apply Rplus_le_compat with (1 := proj2 (proj2 Hx)) (2 := proj2 (proj2 Hy)).
Qed.

Definition add_aa_n_helper (xi yi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (Fminus2 (lower yi) (upper xi)) &&
 Fle2 (Fplus2 (upper xi) (upper yi)) (upper zi).

Theorem add_aa_n :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 add_aa_n_helper xi yi zi = true ->
 ABS (x + y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fminus2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fplus2_correct. clear H3. intro H3.
split.
exact H1.
split.
apply Rle_trans with (Rabs y - Rabs x)%R.
apply Rle_trans with (1 := H2).
unfold Rminus.
apply Rplus_le_compat with (1 := proj1 (proj2 Hy)).
apply Ropp_le_contravar with (1 := proj2 (proj2 Hx)).
replace (x + y)%R with (y - -x)%R. 2: ring.
rewrite<- (Rabs_Ropp x).
apply Rabs_triang_inv.
apply Rle_trans with (Rabs x + Rabs y)%R.
apply Rabs_triang.
apply Rle_trans with (2 := H3).
apply Rplus_le_compat with (1 := proj2 (proj2 Hx)) (2 := proj2 (proj2 Hy)).
Qed.

Theorem sub_aa_p :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 add_aa_p_helper xi yi zi = true ->
 ABS (x - y) zi.
intros x y xi yi zi Hx Hy Hb.
unfold Rminus.
apply add_aa_p with xi yi.
exact Hx.
unfold ABS.
rewrite Rabs_Ropp.
exact Hy.
exact Hb.
Qed.

Theorem sub_aa_o :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 add_aa_o_helper xi yi zi = true ->
 ABS (x - y) zi.
intros x y xi yi zi Hx Hy Hb.
unfold Rminus.
apply add_aa_o with xi yi.
exact Hx.
unfold ABS.
rewrite Rabs_Ropp.
exact Hy.
exact Hb.
Qed.

Theorem sub_aa_n :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 add_aa_n_helper xi yi zi = true ->
 ABS (x - y) zi.
intros x y xi yi zi Hx Hy Hb.
unfold Rminus.
apply add_aa_n with xi yi.
exact Hx.
unfold ABS.
rewrite Rabs_Ropp.
exact Hy.
exact Hb.
Qed.

End Gappa_pred_abs.
