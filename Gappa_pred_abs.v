Require Import Gappa_common.
Require Import Gappa_pred_nzr.

Section Gappa_pred_abs.

Lemma Rabs_def2b :
 forall x a : R, (Rabs x <= a)%R -> (-a <= x <= a)%R.
intros x a H.
split.
case (Rcase_abs x); intros.
rewrite Rabs_left with (1 := r) in H.
rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar with (1 := H).
apply Rle_trans with R0.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply Rle_trans with (2 := H).
apply Rabs_pos.
apply Rge_le with (1 := r).
apply Rle_trans with (2 := H).
apply RRle_abs.
Qed.

Definition bnd_of_abs_helper (xi zi : FF) :=
 Fle2 (lower zi) (Fopp2 (upper xi)) &&
 Fle2 (upper xi) (upper zi).

Theorem bnd_of_abs :
 forall x : R, forall xi zi : FF,
 ABS x xi ->
 bnd_of_abs_helper xi zi = true ->
 BND x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fopp2_correct. fold float2R. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
assert (H : (-(upper xi) <= x <= (upper xi))%R).
apply (Rabs_def2b _ _ (proj2 (proj2 Hx))).
split.
apply Rle_trans with (1 := H1) (2 := proj1 H).
apply Rle_trans with (1 := proj2 H) (2 := H2).
Qed.

Theorem abs_of_uabs :
 forall x : R, forall zi : FF,
 BND (Rabs x) zi ->
 Fpos0 (lower zi) = true ->
 ABS x zi.
intros x zi Hx Hb.
generalize (Fpos0_correct _ Hb). clear Hb. intro H1.
exact (conj H1 Hx).
Qed.

Theorem uabs_of_abs :
 forall x : R, forall zi : FF,
 ABS x zi ->
 BND (Rabs x) zi.
intros x zi (_,Hx2).
exact Hx2.
Qed.

Definition abs_of_bnd_p_helper (xi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem abs_of_bnd_p :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 abs_of_bnd_p_helper xi zi = true ->
 ABS x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
split.
exact H1.
apply IRabs_p with (2 := H2) (3 := H3) (4 := Hx).
apply Rle_trans with (1 := H1) (2 := H2).
Qed.

Definition abs_of_bnd_o_helper (xi zi : FF) :=
 Fis0 (lower zi) &&
 Fle2 (upper xi) (upper zi) &&
 Fle2 (Fopp2 (lower xi)) (upper zi).

Theorem abs_of_bnd_o :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 abs_of_bnd_o_helper xi zi = true ->
 ABS x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fis0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fopp2_correct. clear H3. intro H3.
split.
rewrite H1.
apply Rle_refl.
apply IRabs_o with (2 := H3) (3 := H2) (4 := Hx).
rewrite H1.
apply Rle_refl.
Qed.

Definition abs_of_bnd_n_helper (xi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (Fopp2 (upper xi)) &&
 Fle2 (Fopp2 (lower xi)) (upper zi).

Theorem abs_of_bnd_n :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 abs_of_bnd_n_helper xi zi = true ->
 ABS x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fopp2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fopp2_correct. clear H3. intro H3.
split.
exact H1.
apply IRabs_n with (2 := H2) (3 := H3) (4 := Hx).
apply Ropp_le_cancel.
rewrite Ropp_0.
apply Rle_trans with (1 := H1) (2 := H2).
Qed.

Definition abs_subset_helper (xi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem abs_subset :
 forall x : R, forall xi zi : FF,
 ABS x xi ->
 abs_subset_helper xi zi = true ->
 ABS x zi.
intros x xi zi (Hx1,Hx2) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
split.
exact H1.
apply IRsubset with (1 := H2) (2 := H3) (3 := Hx2).
Qed.

Definition intersect_aa_helper (xf yf : float2) (zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) yf &&
 Fle2 xf (upper zi).

Theorem intersect_aa :
 forall z : R, forall xi yi zi : FF,
 ABS z xi -> ABS z yi ->
 intersect_aa_helper (upper xi) (lower yi) zi = true ->
 ABS z zi.
intros z xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
split.
exact H1.
split.
apply Rle_trans with (1 := H2) (2 := proj1 (proj2 Hy)).
apply Rle_trans with (1 := proj2 (proj2 Hx)) (2 := H3).
Qed.

Theorem absurd_intersect_aa :
 forall z : R, forall xi yi : FF,
 ABS z xi -> ABS z yi ->
 Flt2 (upper xi) (lower yi) = true ->
 contradiction.
intros z xi yi Hx Hy Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ (proj2 (proj2 Hx)) H). clear H. intro H.
generalize (Rlt_le_trans _ _ _ H (proj1 (proj2 Hy))). clear H. intro H.
elim (Rlt_irrefl _ H).
Qed.

Definition mul_aa_helper (xi yi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (lower yi)) &&
 Fle2 (Fmult2 (upper xi) (upper yi)) (upper zi).

Theorem mul_aa :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 mul_aa_helper xi yi zi = true ->
 ABS (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fmult2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
unfold ABS in *.
split.
exact H1.
rewrite Rabs_mult.
apply IRmult_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; intuition.
Qed.

Definition div_aa_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fpos0 (lower zi) &&
 Fle2 (Fmult2 (upper yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult2 (lower yi) (upper zi)).

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
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
split.
exact H2.
replace (Rabs (x / y)) with (Rabs x / Rabs y)%R.
unfold ABS in *.
apply IRdiv_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; intuition.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rabs_Rinv.
apply refl_equal.
apply nzr_of_abs with (1 := Hy) (2 := Hb).
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

Definition bnd_of_bnd_abs_p_helper (xi yi zi : FF) :=
 Flt2 (Fopp2 (lower yi)) (lower xi) &&
 Fle2 (lower zi) (lower yi) &&
 Fle2 (upper xi) (upper zi).

Theorem bnd_of_bnd_abs_p :
 forall x : R, forall xi yi zi : FF,
 BND x xi -> ABS x yi ->
 bnd_of_bnd_abs_p_helper xi yi zi = true ->
 BND x zi.
intros x xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_correct _ _ H1). rewrite Fopp2_correct. fold float2R. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
case (Rcase_abs x) ; intro H.
unfold ABS in Hy.
rewrite (Rabs_left _ H) in Hy.
elim (Rlt_not_le (lower xi) x). 2: exact (proj1 Hx).
apply Rle_lt_trans with (2 := H1).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
exact (proj1 (proj2 Hy)).
unfold ABS in Hy.
rewrite (Rabs_right _ H) in Hy.
split.
apply Rle_trans with (1 := H2) (2 := proj1 (proj2 Hy)).
apply Rle_trans with (1 := proj2 Hx) (2 := H3).
Qed.

Definition bnd_of_bnd_abs_n_helper (xi yi zi : FF) :=
 Flt2 (upper xi) (lower yi) &&
 Fle2 (lower zi) (lower xi) &&
 Fle2 (Fopp2 (lower yi)) (upper zi).

Theorem bnd_of_bnd_abs_n :
 forall x : R, forall xi yi zi : FF,
 BND x xi -> ABS x yi ->
 bnd_of_bnd_abs_n_helper xi yi zi = true ->
 BND x zi.
intros x xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fopp2_correct. fold float2R. clear H3. intro H3.
case (Rcase_abs x) ; intro H.
unfold ABS in Hy.
rewrite (Rabs_left _ H) in Hy.
split.
apply Rle_trans with (1 := H2) (2 := proj1 Hx).
apply Rle_trans with (2 := H3).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
exact (proj1 (proj2 Hy)).
unfold ABS in Hy.
rewrite (Rabs_right _ H) in Hy.
elim (Rlt_not_le x (upper xi)). 2: exact (proj2 Hx).
apply Rlt_le_trans with (1 := H1) (2 := proj1 (proj2 Hy)).
Qed.

End Gappa_pred_abs.
