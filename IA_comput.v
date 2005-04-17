Require Export IA_real.
Require Export AllFloat.

Section IA_comput.

Definition radix := 2%Z.

Definition radixMoreThanOne := TwoMoreThanOne.
Lemma radixNotZero: (0 < radix)%Z.
auto with zarith.
Qed.

Coercion float2R := FtoR radix.
Record FF: Set := makepairF { lower : float ; upper : float }.
Coercion FF2RR := fun x : FF => makepairR (lower x) (upper x).
Definition IintF (xi : FF) (x : R) := IintR xi x.

Definition Fle_b (x y : float) := Fle_bool radix x y.
Lemma Fle_b_correct :
 forall x y : float,
 Fle_b x y = true -> (x <= y)%R.
intros x y H.
apply (Fle_bool_correct_t radix radixMoreThanOne).
exact H.
Qed.

Definition Float1 (x : Z) := x.
Definition Float2 := Float.
Record deci : Set := Float10 { Fnum10 : Z ; Fexp10 : Z }.
Coercion deci2R := fun x : deci => (Fnum10 x * powerRZ 10 (Fexp10 x))%R.

Definition Dcompare (x : float) (y : deci) :=
 let m := Fnum10 y in let e := Fexp10 y in
 let f := Zpower_nat 5 (Zabs_nat e) in
 match e with
   Zpos _ => Fcompare radix x (Float (m * f) e)
 | Zneg _ => Fcompare radix (Float (Fnum x * f) (Fexp x)) (Float m e)
 | Z0 => Fcompare radix x (Float m 0)
 end.

Definition Dle_fd (x : float) (y : deci) :=
 match (Dcompare x y) with
  Gt => false
 | _ => true
 end.

Lemma Dle_fd_correct :
 forall x : float, forall y : deci,
 Dle_fd x y = true ->
 (x <= y)%R.
Admitted.

Definition Dle_df (x : deci) (y : float) :=
 match (Dcompare y x) with
  Lt => false
 | _ => true
 end.

Lemma Dle_df_correct :
 forall x : deci, forall y : float,
 Dle_df x y = true ->
 (x <= y)%R.
Admitted.

Definition constant2_helper (x : float) (zi : FF) :=
 Fle_b (lower zi) x && Fle_b x (upper zi).

Theorem constant2 :
 forall x : float, forall zi : FF,
 constant2_helper x zi = true ->
 IintF zi x.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
split ; assumption.
Qed.

Theorem constant1 :
 forall x : Z, forall zi : FF,
 constant2_helper (Float x 0) zi = true ->
 IintF zi x.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
replace (IZR x) with (float2R (Float x 0)).
split ; assumption.
unfold float2R, FtoR.
simpl.
apply Rmult_1_r.
Qed.

Definition constant10_helper (x : deci) (zi : FF) :=
 Dle_fd (lower zi) x && Dle_df x (upper zi).

Theorem constant10 :
 forall x : deci, forall zi : FF,
 constant10_helper x zi = true ->
 IintF zi x.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Dle_fd_correct _ _ H1). clear H1. intro H1.
generalize (Dle_df_correct _ _ H2). clear H2. intro H2.
split ; assumption.
Qed.

Definition subset_helper (xi zi : FF) :=
 Fle_b (lower zi) (lower xi) &&
 Fle_b (upper xi) (upper zi).

Theorem subset :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 subset_helper xi zi = true ->
 IintF zi x.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 Hx)).
apply Rle_trans with (1 := (proj2 Hx)) (2 := H2).
Qed.

Definition intersect_helper (xi yi zi : FF) :=
 Fle_b (lower zi) (lower yi) &&
 Fle_b (upper xi) (upper zi).

Theorem intersect :
 forall z : R, forall xi yi zi : FF,
 IintF xi z -> IintF yi z ->
 intersect_helper xi yi zi = true ->
 IintF zi z.
intros z xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 Hy)).
apply Rle_trans with (1 := (proj2 Hx)) (2 := H2).
Qed.

Definition neg_helper (xi zi : FF) :=
 Fle_b (lower zi) (Fopp (upper xi)) &&
 Fle_b (Fopp (lower xi)) (upper zi).

Theorem neg :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 neg_helper xi zi = true ->
 IintF zi (-x).
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1).
unfold float2R. rewrite Fopp_correct.
apply Ropp_le_contravar with (1 := (proj2 Hx)).
apply Rle_trans with (2 := H2).
unfold float2R. rewrite Fopp_correct.
apply Ropp_le_contravar with (1 := (proj1 Hx)).
Qed.

Definition add_helper (xi yi zi : FF) :=
 Fle_b (lower zi) (Fplus radix (lower xi) (lower yi)) &&
 Fle_b (Fplus radix (upper xi) (upper yi)) (upper zi).

Theorem add :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 add_helper xi yi zi = true ->
 IintF zi (x + y).
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). rewrite Fplus_correct with (1 := radixNotZero). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). rewrite Fplus_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (IplusR_fun_correct xi yi _ _ Hx Hy). intro H.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 H)).
apply Rle_trans with (1 := (proj2 H)) (2 := H2).
Qed.

Definition sub_helper (xi yi zi : FF) :=
 Fle_b (lower zi) (Fminus radix (lower xi) (upper yi)) &&
 Fle_b (Fminus radix (upper xi) (lower yi)) (upper zi).

Theorem sub :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 sub_helper xi yi zi = true ->
 IintF zi (x - y).
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). rewrite Fminus_correct with (1 := radixNotZero). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). rewrite Fminus_correct with (1 := radixNotZero). clear H2. intro H2.
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

Definition contains_zero_helper (zi : FF) :=
 Fneg0 (lower zi) &&
 Fpos0 (upper zi).

Lemma contains_zero :
 forall zi : FF,
 contains_zero_helper zi = true ->
 IintF zi 0.
intros zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
split ; assumption.
Qed.

Lemma sub_refl :
 forall x : R, forall zi : FF,
 contains_zero_helper zi = true ->
 IintF zi (x - x).
intros x zi Hb.
replace (x - x)%R with R0.
apply contains_zero with (1 := Hb).
rewrite <- Rplus_opp_r with x.
apply refl_equal.
Qed.

Definition mul_pp_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fpos (lower yi) &&
 Fle_b (lower zi) (Fmult (lower xi) (lower yi)) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_pp :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_pp_helper xi yi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
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
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_pn_helper xi yi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
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
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_pn_helper yi xi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
apply mul_pn with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_nn_helper (xi yi zi : FF) :=
 Fneg (upper xi) &&
 Fneg (upper yi) &&
 Fle_b (lower zi) (Fmult (upper xi) (upper yi)) &&
 Fle_b (Fmult (lower xi) (lower yi)) (upper zi).

Theorem mul_nn :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_nn_helper xi yi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
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

Definition mul_po_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle_b (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_po :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_po_helper xi yi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
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

Theorem mul_op :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_po_helper yi xi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
apply mul_po with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_no_helper (xi yi zi : FF) :=
 Fneg (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle_b (lower zi) (Fmult (lower xi) (upper yi)) &&
 Fle_b (Fmult (lower xi) (lower yi)) (upper zi).

Theorem mul_no :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_no_helper xi yi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
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

Theorem mul_on :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_no_helper yi xi zi = true ->
 IintF zi (x * y).
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
apply mul_no with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_oo_helper (xi yi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle_b (lower zi) (Fmult (lower xi) (upper yi)) &&
 Fle_b (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle_b (Fmult (lower xi) (lower yi)) (upper zi) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_oo :
 forall x y : R, forall xi yi zi : FF,
 IintF xi x -> IintF yi y ->
 mul_oo_helper xi yi zi = true ->
 IintF zi (x * y).
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
generalize (Fle_b_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
generalize (Fle_b_correct _ _ H6). rewrite Fmult_correct with (1 := radixNotZero). clear H6. intro H6.
generalize (Fle_b_correct _ _ H7). rewrite Fmult_correct with (1 := radixNotZero). clear H7. intro H7.
generalize (Fle_b_correct _ _ H8). rewrite Fmult_correct with (1 := radixNotZero). clear H8. intro H8.
unfold IintF, IintR.
apply ImultR_mm with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition square_p_helper (xi zi : FF) :=
 Fpos (lower xi) &&
 Fle_b (lower zi) (Fmult (lower xi) (lower xi)) &&
 Fle_b (Fmult (upper xi) (upper xi)) (upper zi).

Theorem square_p :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 square_p_helper xi zi = true ->
 IintF zi (x * x).
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). rewrite Fmult_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
unfold IintF, IintR.
apply ImultR_pp with (lower xi) (upper xi) (lower xi) (upper xi)
 ; auto with real.
Qed.

Definition square_n_helper (xi zi : FF) :=
 Fneg (upper xi) &&
 Fle_b (lower zi) (Fmult (upper xi) (upper xi)) &&
 Fle_b (Fmult (lower xi) (lower xi)) (upper zi).

Theorem square_n :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 square_n_helper xi zi = true ->
 IintF zi (x * x).
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). rewrite Fmult_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
unfold IintF, IintR.
apply ImultR_nn with (lower xi) (upper xi) (lower xi) (upper xi)
 ; auto with real.
Qed.

Definition square_o_helper (xi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower zi) &&
 Fle_b (Fmult (upper xi) (upper xi)) (upper zi) &&
 Fle_b (Fmult (lower xi) (lower xi)) (upper zi).

Theorem square_o :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 square_o_helper xi zi = true ->
 IintF zi (x * x).
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H5).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fneg0_correct _ H3). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle_b_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold IintF, IintR.
split.
replace (x * x)%R with (Rsqr x). 2: trivial.
apply Rle_trans with 0%R ; auto with real.
case (Rlt_le_dec 0 x); intro H.
generalize (Rlt_le _ _ H). clear H. intro H.
generalize (proj2 Hx). intro H0.
apply Rle_trans with ((upper xi) * (upper xi))%R ; auto with real.
apply Rle_trans with ((lower xi) * (lower xi))%R.
2: exact H5.
apply Rle_trans with (x * lower xi)%R.
exact (monotony_1n _ _ _ H (proj1 Hx)).
exact (monotony_2n _ _ _ H1 (proj1 Hx)).
Qed.

End IA_comput.
