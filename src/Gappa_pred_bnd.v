Require Import Gappa_common.
Require Import Gappa_decimal.

Section Gappa_pred_bnd.

Definition Float1 := Z2R.

Definition constant2_helper (x : float2) (zi : FF) :=
 Fle2 (lower zi) x && Fle2 x (upper zi).

Theorem constant2 :
 forall x : float2, forall zi : FF,
 constant2_helper x zi = true ->
 BND x zi.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split ; assumption.
Qed.

Theorem constant1 :
 forall x : Z, forall zi : FF,
 constant2_helper (Float2 x 0) zi = true ->
 BND (Float1 x) zi.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
rewrite <- (Rmult_1_r (Float1 x)).
change (Float1 x * 1)%R with (float2R (Float2 x 0)).
split ; assumption.
Qed.

Definition constant10_helper (x : float10) (zi : FF) :=
 Dle_fd (lower zi) x && Dle_df x (upper zi).

Theorem constant10 :
 forall x : float10, forall zi : FF,
 constant10_helper x zi = true ->
 BND x zi.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Dle_fd_correct _ _ H1). clear H1. intro H1.
generalize (Dle_df_correct _ _ H2). clear H2. intro H2.
split ; assumption.
Qed.

Definition subset_helper (xi zi : FF) :=
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem subset :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 subset_helper xi zi = true ->
 BND x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
apply IRsubset with (1 := H1) (2 := H2) (3 := Hx).
Qed.

Theorem subset_l :
 forall x : R, forall xi : FF, forall f : float2,
 BND x xi ->
 Fle2 f (lower xi) = true ->
 (f <= x)%R.
intros x xi f Hx Hb.
generalize (Fle2_correct _ _ Hb). clear Hb. intro H1.
apply Rle_trans with (1 := H1).
exact (proj1 Hx).
Qed.

Theorem subset_r :
 forall x : R, forall xi : FF, forall f : float2,
 BND x xi ->
 Fle2 (upper xi) f = true ->
 (x <= f)%R.
intros x xi f Hx Hb.
generalize (Fle2_correct _ _ Hb). clear Hb. intro H1.
apply Rle_trans with (2 := H1).
exact (proj2 Hx).
Qed.

Definition intersect_helper (xf yf : float2) (zi : FF) :=
 Fle2 (lower zi) yf &&
 Fle2 xf (upper zi).

Theorem intersect :
 forall z : R, forall xi yi zi : FF,
 BND z xi -> BND z yi ->
 intersect_helper (upper xi) (lower yi) zi = true ->
 BND z zi.
intros z xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1) (2 := (proj1 Hy)).
apply Rle_trans with (1 := (proj2 Hx)) (2 := H2).
Qed.

Theorem intersect_hb :
 forall z : R, forall xf : float2, forall yi zi : FF,
 (z <= xf)%R -> BND z yi ->
 intersect_helper xf (lower yi) zi = true ->
 BND z zi.
intros z xf yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1) (2 := (proj1 Hy)).
apply Rle_trans with (1 := Hx) (2 := H2).
Qed.

Theorem intersect_bh :
 forall z : R, forall yf : float2, forall xi zi : FF,
 BND z xi -> (yf <= z)%R ->
 intersect_helper (upper xi) yf zi = true ->
 BND z zi.
intros z yf xi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1) (2 := Hy).
apply Rle_trans with (1 := (proj2 Hx)) (2 := H2).
Qed.

Theorem absurd_intersect :
 forall z : R, forall xi yi : FF,
 BND z xi -> BND z yi ->
 Flt2 (upper xi) (lower yi) = true ->
 contradiction.
intros z xi yi Hx Hy Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ (proj2 Hx) H). clear H. intro H.
generalize (Rlt_le_trans _ _ _ H (proj1 Hy)). clear H. intro H.
elim (Rlt_irrefl _ H).
Qed.

Theorem absurd_intersect_hb :
 forall z : R, forall xf : float2, forall yi : FF,
 (z <= xf)%R -> BND z yi ->
 Flt2 xf (lower yi) = true ->
 contradiction.
intros z xi yi Hx Hy Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ Hx H). clear H. intro H.
generalize (Rlt_le_trans _ _ _ H (proj1 Hy)). clear H. intro H.
elim (Rlt_irrefl _ H).
Qed.

Theorem absurd_intersect_bh :
 forall z : R, forall xi : FF, forall yf : float2,
 BND z xi -> (yf <= z)%R ->
 Flt2 (upper xi) yf = true ->
 contradiction.
intros z xi yi Hx Hy Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ (proj2 Hx) H). clear H. intro H.
generalize (Rlt_le_trans _ _ _ H Hy). clear H. intro H.
elim (Rlt_irrefl _ H).
Qed.

Theorem union :
 forall x : R, forall P : Prop, forall xi xi1 : FF,
 (BND x xi1 -> P) ->
 Fle2 (lower xi1) (lower xi) = true ->
 (BND x (makepairF (upper xi1) (upper xi)) -> P) ->
 BND x xi -> P.
intros x P xi xi1 Hx1 Hb Hx2 Hx.
generalize (Fle2_correct _ _ Hb). clear Hb. intro H1.
case (Rlt_le_dec x (upper xi1)) ; intro H.
apply Hx1.
split ; auto with real.
apply Rle_trans with (1 := H1) (2 := (proj1 Hx)).
apply Hx2.
split.
exact H.
exact (proj2 Hx).
Qed.

Definition neg_helper (xi zi : FF) :=
 Fle2 (lower zi) (Fopp2 (upper xi)) &&
 Fle2 (Fopp2 (lower xi)) (upper zi).

Theorem neg :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 neg_helper xi zi = true ->
 BND (-x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fopp2_correct. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fopp2_correct. clear H2. intro H2.
apply IRopp with (1 := H1) (2 := H2) (3 := Hx).
Qed.

Definition add_helper (xi yi zi : FF) :=
 Fle2 (lower zi) (Fplus2 (lower xi) (lower yi)) &&
 Fle2 (Fplus2 (upper xi) (upper yi)) (upper zi).

Theorem add :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 add_helper xi yi zi = true ->
 BND (x + y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fplus2_correct. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fplus2_correct. clear H2. intro H2.
apply IRplus with (1 := H1) (2 := H2) (3 := Hx) (4 := Hy).
Qed.

Definition sub_helper (xi yi zi : FF) :=
 Fle2 (lower zi) (Fminus2 (lower xi) (upper yi)) &&
 Fle2 (Fminus2 (upper xi) (lower yi)) (upper zi).

Theorem sub :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 sub_helper xi yi zi = true ->
 BND (x - y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fminus2_correct. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fminus2_correct. clear H2. intro H2.
apply IRminus with (1 := H1) (2 := H2) (3 := Hx) (4 := Hy).
Qed.

Definition not_zero (zi : FF) :=
 Fpos (lower zi) || Fneg (upper zi).

Lemma not_zero_correct :
 forall z : R, forall zi : FF,
 BND z zi ->
 not_zero zi = true ->
 (z <> 0)%R.
intros z zi Hz Hb.
apply Rlt_dichotomy_converse.
generalize (orb_prop _ _ Hb). clear Hb.
intro H. elim H; clear H; intro H.
right.
generalize (Fpos_correct _ H). clear H. intro H.
unfold Rgt.
apply Rlt_le_trans with (1 := H).
exact (proj1 Hz).
left.
generalize (Fneg_correct _ H). clear H. intro H.
apply Rle_lt_trans with (2 := H).
exact (proj2 Hz).
Qed.

Definition contains_zero_helper (zi : FF) :=
 Fneg0 (lower zi) &&
 Fpos0 (upper zi).

Lemma contains_zero :
 forall zi : FF,
 contains_zero_helper zi = true ->
 BND 0 zi.
intros zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
split ; assumption.
Qed.

Lemma sub_refl :
 forall x : R, forall zi : FF,
 contains_zero_helper zi = true ->
 BND (x - x) zi.
intros x zi Hb.
unfold Rminus.
rewrite (Rplus_opp_r x).
apply contains_zero with (1 := Hb).
Qed.

Definition div_refl_helper (zi : FF) :=
 Fle2 (lower zi) (Float2 1 0) &&
 Fle2 (Float2 1 0) (upper zi).

Lemma div_refl :
 forall x : R, forall zi : FF,
 NZR x ->
 div_refl_helper zi = true ->
 BND (x / x) zi.
intros x zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
assert (Float2 1 0 = 1 :>R)%R.
apply Rmult_1_r.
generalize (Fle2_correct _ _ H1). clear H1. rewrite H. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. rewrite H. intro H2.
unfold Rdiv.
rewrite Rinv_r. 2: exact Hx.
exact (conj H1 H2).
Qed.

Definition mul_pp_helper (xi yi zi : FF) :=
 Fpos0 (lower xi) &&
 Fpos0 (lower yi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (lower yi)) &&
 Fle2 (Fmult2 (upper xi) (upper yi)) (upper zi).

Theorem mul_pp :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_pp_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRmult_pp with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Definition mul_pn_helper (xi yi zi : FF) :=
 Fpos0 (lower xi) &&
 Fneg0 (upper yi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (lower yi)) &&
 Fle2 (Fmult2 (lower xi) (upper yi)) (upper zi).

Theorem mul_pn :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_pn_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRmult_pn with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Definition mul_np_helper (xi yi zi : FF) := mul_pn_helper yi xi zi.

Theorem mul_np :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_np_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
exact (mul_pn _ _ _ _ _ Hy Hx Hb).
Qed.

Definition mul_nn_helper (xi yi zi : FF) :=
 Fneg0 (upper xi) &&
 Fneg0 (upper yi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (upper yi)) &&
 Fle2 (Fmult2 (lower xi) (lower yi)) (upper zi).

Theorem mul_nn :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_nn_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRmult_nn with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Definition mul_po_helper (xi yi zi : FF) :=
 Fpos0 (lower xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (lower yi)) &&
 Fle2 (Fmult2 (upper xi) (upper yi)) (upper zi).

Theorem mul_po :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_po_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
apply IRmult_po with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := H5) (6 := Hx) (7 := Hy).
Qed.

Definition mul_op_helper (xi yi zi : FF) := mul_po_helper yi xi zi.

Theorem mul_op :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_po_helper yi xi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
exact (mul_po _ _ _ _ _ Hy Hx Hb).
Qed.

Definition mul_no_helper (xi yi zi : FF) :=
 Fneg0 (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (upper yi)) &&
 Fle2 (Fmult2 (lower xi) (lower yi)) (upper zi).

Theorem mul_no :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_no_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
apply IRmult_no with (1 := H1) (2 := H2) (3 := H3) (4 := H4) (5 := H5) (6 := Hx) (7 := Hy).
Qed.

Definition mul_on_helper (xi yi zi : FF) := mul_no_helper yi xi zi.

Theorem mul_on :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_no_helper yi xi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
exact (mul_no _ _ _ _ _ Hy Hx Hb).
Qed.

Definition mul_oo_helper (xi yi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (upper yi)) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (lower yi)) &&
 Fle2 (Fmult2 (lower xi) (lower yi)) (upper zi) &&
 Fle2 (Fmult2 (upper xi) (upper yi)) (upper zi).

Theorem mul_oo :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_oo_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H8).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H7).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H6).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fneg0_correct _ H3). clear H3. intro H3.
generalize (Fpos0_correct _ H4). clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
generalize (Fle2_correct _ _ H6). rewrite Fmult2_correct. clear H6. intro H6.
generalize (Fle2_correct _ _ H7). rewrite Fmult2_correct. clear H7. intro H7.
generalize (Fle2_correct _ _ H8). rewrite Fmult2_correct. clear H8. intro H8.
exact (IRmult_oo _ _ _ _ _ _ H1 H2 H3 H4 H6 H5 H7 H8 _ _ Hx Hy).
Qed.

Definition square_p_helper (xi zi : FF) :=
 Fpos0 (lower xi) &&
 Fle2 (lower zi) (Fmult2 (lower xi) (lower xi)) &&
 Fle2 (Fmult2 (upper xi) (upper xi)) (upper zi).

Theorem square_p :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 square_p_helper xi zi = true ->
 BND (x * x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply mul_pp with (1 := Hx) (2 := Hx).
unfold mul_pp_helper.
rewrite H1. rewrite H2. rewrite H3.
apply refl_equal.
Qed.

Definition square_n_helper (xi zi : FF) :=
 Fneg0 (upper xi) &&
 Fle2 (lower zi) (Fmult2 (upper xi) (upper xi)) &&
 Fle2 (Fmult2 (lower xi) (lower xi)) (upper zi).

Theorem square_n :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 square_n_helper xi zi = true ->
 BND (x * x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
apply mul_nn with (1 := Hx) (2 := Hx).
unfold mul_nn_helper.
rewrite H1. rewrite H2. rewrite H3.
apply refl_equal.
Qed.

Definition square_o_helper (xi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower zi) &&
 Fle2 (Fmult2 (upper xi) (upper xi)) (upper zi) &&
 Fle2 (Fmult2 (lower xi) (lower xi)) (upper zi).

Theorem square_o :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 square_o_helper xi zi = true ->
 BND (x * x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fneg0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
apply IRsquare_o with (1 := H1) (2 := H2) (3 := H3) (4 := H5) (5 := H4) (6 := Hx).
Qed.

Definition div_pp_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fpos0 (lower xi) &&
 Fle2 (Fmult2 (upper yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult2 (lower yi) (upper zi)).

Theorem div_pp :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 div_pp_helper xi yi zi = true ->
 BND (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRdiv_pp with (1 := H2) (2 := H1) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Definition div_op_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fle2 (Fmult2 (lower yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult2 (lower yi) (upper zi)).

Theorem div_op :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 div_op_helper xi yi zi = true ->
 BND (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
apply IRdiv_op with (1 := H2) (2 := H3) (3 := H1) (4 := H4) (5 := H5) (6 := Hx) (7 := Hy).
Qed.

Definition div_np_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fneg0 (upper xi) &&
 Fle2 (Fmult2 (lower yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult2 (upper yi) (upper zi)).

Theorem div_np :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 div_np_helper xi yi zi = true ->
 BND (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRdiv_np with (1 := H2) (2 := H1) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Definition div_pn_helper (xi yi zi : FF) :=
 Fneg (upper yi) &&
 Fpos0 (lower xi) &&
 Fle2 (upper xi) (Fmult2 (upper yi) (lower zi)) &&
 Fle2 (Fmult2 (lower yi) (upper zi)) (lower xi).

Theorem div_pn :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 div_pn_helper xi yi zi = true ->
 BND (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRdiv_pn with (1 := H2) (2 := H1) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Definition div_on_helper (xi yi zi : FF) :=
 Fneg (upper yi) &&
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fle2 (upper xi) (Fmult2 (upper yi) (lower zi)) &&
 Fle2 (Fmult2 (upper yi) (upper zi)) (lower xi).

Theorem div_on :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 div_on_helper xi yi zi = true ->
 BND (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult2_correct. clear H5. intro H5.
apply IRdiv_on with (1 := H2) (2 := H3) (3 := H1) (4 := H4) (5 := H5) (6 := Hx) (7 := Hy).
Qed.

Definition div_nn_helper (xi yi zi : FF) :=
 Fneg (upper yi) &&
 Fneg0 (upper xi) &&
 Fle2 (upper xi) (Fmult2 (lower yi) (lower zi)) &&
 Fle2 (Fmult2 (upper yi) (upper zi)) (lower xi).

Theorem div_nn :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 div_nn_helper xi yi zi = true ->
 BND (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult2_correct. clear H4. intro H4.
apply IRdiv_nn with (1 := H2) (2 := H1) (3 := H3) (4 := H4) (5 := Hx) (6 := Hy).
Qed.

Lemma Rabs_idem :
 forall x : R, (x <= Rabs x)%R.
intro x.
unfold Rabs. case Rcase_abs ; intro H.
apply Rle_trans with (1 := (Rlt_le _ _ H)).
auto with real.
apply Req_le.
apply refl_equal.
Qed.

Definition invert_abs_helper (xi zi : FF) :=
 Fle2 (lower zi) (Fopp2 (upper xi)) &&
 Fle2 (upper xi) (upper zi).

Theorem invert_abs :
 forall x : R, forall xi zi : FF,
 BND (Rabs x) xi ->
 invert_abs_helper xi zi = true ->
 BND x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fopp2_correct. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (2 := proj2 Hx).
pattern x at 2 ; rewrite <- Ropp_involutive.
rewrite Rabs_Ropp.
apply Rabs_idem.
apply Rle_trans with (2 := H2).
apply Rle_trans with (1 := Rabs_idem x) (2 := proj2 Hx).
Qed.

Definition sqrt_helper (xi zi : FF) :=
 (if (Fneg0 (lower zi)) then Fpos0 (lower xi)
  else Fle2 (Fmult2 (lower zi) (lower zi)) (lower xi)) &&
 Fpos0 (upper zi) &&
 Fle2 (upper xi) (Fmult2 (upper zi) (upper zi)).

Theorem sqrtG:
 forall x : R, forall xi zi : FF,
 BND x xi ->
 sqrt_helper xi zi = true ->
 BND (sqrt x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult2_correct. clear H3. intro H3.
unfold BND.
apply IRsqrt with (2 := H2) (3 := H3) (4 := Hx).
induction (lower zi).
induction Fnum ; simpl in H1.
rewrite float2_zero.
rewrite Rmult_0_l.
assert (H4 := Fpos0_correct _ H1).
case (Rlt_le_dec 0 0) ; intros _ ; exact H4.
case (Rlt_le_dec 0 (Float2 (Zpos p) Fexp)).
intros _.
rewrite <- Fmult2_correct.
apply Fle2_correct.
exact H1.
intro H.
elim (Rlt_irrefl R0).
apply Rlt_le_trans with (2 := H).
apply Fpos_correct.
apply refl_equal.
case (Rlt_le_dec 0 (Float2 (Zneg p) Fexp)).
intro H.
elim (Rlt_irrefl R0).
apply Rlt_trans with (1 := H).
apply Fneg_correct.
apply refl_equal.
intros _.
apply Fpos0_correct.
exact H1.
Qed.

End Gappa_pred_bnd.
