Require Export IA_real.
Require Export AllFloat.

Section IA_comput.

Definition radix := 2%Z.

Definition radixMoreThanOne := TwoMoreThanOne.
Lemma radixNotZero: (0 < radix)%Z.
auto with zarith.
Qed.

Coercion Local float2R := FtoR radix.
Record FF: Set := makepairF { lower : float ; upper : float }.
Coercion Local FF2RR := fun x : FF => makepairR (lower x) (upper x).
Definition IintF (xi : FF) (x : R) := IintR xi x.

Definition Fle_b (x y : float) := Fle_bool radix x y.
Lemma Fle_b_correct :
 forall x y : float,
 Fle_b x y = true -> (x <= y)%R.
intros x y H.
apply (Fle_bool_correct_t radix radixMoreThanOne).
exact H.
Qed.

Definition add_helper (xi yi zi : FF) :=
 andb
  (Fle_b (lower zi) (Fplus radix (lower xi) (lower yi)))
  (Fle_b (Fplus radix (upper xi) (upper yi)) (upper zi)).

Theorem add :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 add_helper xi yi zi = true ->
 IintF zi (x + y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1).
rewrite Fplus_correct with (1 := radixNotZero).
clear H1. intro H1.
generalize (Fle_b_correct _ _ H2).
rewrite Fplus_correct with (1 := radixNotZero).
clear H2. intro H2.
generalize (IplusR_fun_correct xi yi _ _ Hx Hy). intro H.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 H)).
apply Rle_trans with (1 := (proj2 H)) (2 := H2).
Qed.

Definition sub_helper (xi yi zi : FF) :=
 andb
  (Fle_b (lower zi) (Fminus radix (lower xi) (upper yi)))
  (Fle_b (Fminus radix (upper xi) (lower yi)) (upper zi)).

Theorem sub :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 sub_helper xi yi zi = true ->
 IintF zi (x - y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1).
rewrite Fminus_correct with (1 := radixNotZero).
clear H1. intro H1.
generalize (Fle_b_correct _ _ H2).
rewrite Fminus_correct with (1 := radixNotZero).
clear H2. intro H2.
generalize (IminusR_fun_correct xi yi _ _ Hx Hy). intro H.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 H)).
apply Rle_trans with (1 := (proj2 H)) (2 := H2).
Qed.

Definition Fpos (x : float) :=
 match (Fnum x) with
   Zpos _ => true
 | _ => false
 end.

Lemma Fpos_correct :
 forall x : float,
 Fpos x = true -> (0 < x)%R.
intros x H.
unfold float2R, FtoR.
apply Rmult_lt_0_compat.
2: auto with real.
generalize H. clear H.
unfold IZR, Fpos.
induction (Fnum x) ; intro H0 ; try discriminate.
apply INR_pos.
Qed.

Definition Fneg (x : float) :=
 match (Fnum x) with
   Zneg _ => true
 | _ => false
 end.

Lemma Fneg_correct :
 forall x : float,
 Fneg x = true -> (x < 0)%R.
intros x H.
unfold float2R, FtoR.
replace (IZR (Fnum x)) with (-(IZR (- Fnum x)))%R.
2: rewrite Ropp_Ropp_IZR ; auto with real.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_gt_0_contravar.
unfold Rgt.
apply Rmult_lt_0_compat.
2: auto with real.
generalize H. clear H.
unfold IZR, Fneg.
induction (Fnum x) ; intro H0 ; try discriminate.
unfold Zopp.
apply INR_pos.
Qed.

Definition Fpos0 (x : float) :=
 match (Fnum x) with
   Zneg _ => false
 | _ => true
 end.

Lemma Fpos0_correct :
 forall x : float,
 Fpos0 x = true -> (0 <= x)%R.
intros x H.
unfold float2R, FtoR.
apply Rmult_le_pos.
2: auto with real.
generalize H. clear H.
unfold IZR, Fpos0.
induction (Fnum x) ; intro H0 ; try discriminate
 ; auto with real.
Qed.

Definition Fneg0 (x : float) :=
 match (Fnum x) with
   Zpos _ => false
 | _ => true
 end.

Lemma Fneg0_correct :
 forall x : float,
 Fneg0 x = true -> (x <= 0)%R.
intros x H.
unfold float2R, FtoR.
replace (IZR (Fnum x)) with (-(IZR (- Fnum x)))%R.
2: rewrite Ropp_Ropp_IZR ; auto with real.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply Rmult_le_pos.
2: auto with real.
generalize H. clear H.
unfold IZR, Fneg0.
induction (Fnum x) ; intro H0 ; try discriminate
 ; unfold Zopp ; auto with real.
Qed.

Definition mul_pp_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fpos (lower yi) &&
 Fle_b (lower zi) (Fmult (lower xi) (lower yi)) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_pp :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_pp_helper xi yi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold IintF, IintR.
apply ImultR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition mul_pn_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fneg (upper yi) &&
 Fle_b (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle_b (Fmult (lower xi) (upper yi)) (upper zi).

Theorem mul_pn :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_pn_helper xi yi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fneg_correct _ H2). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold IintF, IintR.
apply ImultR_pn with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Theorem mul_np :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_pn_helper yi xi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
rewrite Rmult_comm.
apply mul_pn with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_nn_helper (xi yi zi : FF) :=
 Fneg (upper xi) &&
 Fneg (upper yi) &&
 Fle_b (lower zi) (Fmult (upper xi) (upper yi)) &&
 Fle_b (Fmult (lower xi) (lower yi)) (upper zi).

Theorem mul_nn :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_nn_helper xi yi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fneg_correct _ H2). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold IintF, IintR.
apply ImultR_nn with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition mul_pm_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle_b (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_pm :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_pm_helper xi yi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle_b_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold IintF, IintR.
apply ImultR_pm with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Theorem mul_mp :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_pm_helper yi xi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
rewrite Rmult_comm.
apply mul_pm with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_nm_helper (xi yi zi : FF) :=
 Fneg (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle_b (lower zi) (Fmult (lower xi) (upper yi)) &&
 Fle_b (Fmult (lower xi) (lower yi)) (upper zi).

Theorem mul_nm :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_nm_helper xi yi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle_b_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold IintF, IintR.
apply ImultR_nm with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Theorem mul_mn :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_nm_helper yi xi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
rewrite Rmult_comm.
apply mul_nm with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_mm_helper (xi yi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle_b (lower zi) (Fmult (lower xi) (upper yi)) &&
 Fle_b (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle_b (Fmult (lower xi) (lower yi)) (upper zi) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_mm :
 forall xi yi zi : FF, forall x y : R,
 IintF xi x -> IintF yi y ->
 mul_mm_helper xi yi zi = true ->
 IintF zi (x * y).
intros xi yi zi x y Hx Hy Hb.
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
generalize (Fle_b_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
generalize (Fle_b_correct _ _ H6). rewrite Fmult_correct with (1 := radixNotZero). clear H6. intro H6.
generalize (Fle_b_correct _ _ H7). rewrite Fmult_correct with (1 := radixNotZero). clear H7. intro H7.
generalize (Fle_b_correct _ _ H8). rewrite Fmult_correct with (1 := radixNotZero). clear H8. intro H8.
unfold IintF, IintR.
apply ImultR_mm with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.


End IA_comput.
