Require Import AllFloat.
Require Import Gappa_common.

Section Gappa_pred_bnd.

Definition Float1 (x : Z) := x.
Definition Float2 := Float.
Record deci : Set := Float10 { Fnum10 : Z ; Fexp10 : Z }.
Coercion deci2R := fun x : deci => (Fnum10 x * powerRZ 10 (Fexp10 x))%R.


Lemma Fcompare_Eq :
 forall x y : float,
 Fcompare radix x y = Eq ->
 float2R x = float2R y.
intros x y H.
apply Feq_bool_correct_t with (1 := radixMoreThanOne).
unfold radix in H.
unfold Feq_bool. rewrite H. trivial.
Qed.

Lemma Fcompare_Lt :
 forall x y : float,
 Fcompare radix x y = Lt ->
 (x < y)%R.
intros x y H.
apply Flt_bool_correct_t with (1 := radixMoreThanOne).
unfold radix in H.
unfold Flt_bool. rewrite H. trivial.
Qed.

Lemma Fcompare_Gt :
 forall x y : float,
 Fcompare radix x y = Gt ->
 (x > y)%R.
intros x y H.
unfold float2R.
apply Flt_Fgt.
apply Fle_bool_correct_f with (1 := radixMoreThanOne).
unfold radix in H.
unfold Fle_bool. rewrite H. trivial.
Qed.

Definition Dcompare (x : float) (y : deci) :=
 let m := Fnum10 y in let e := Fexp10 y in
 match e with
 | Zpos p => Fcompare radix x (Float (m * Zpower_pos 5 p) e)
 | Zneg p => Fcompare radix (Float (Fnum x * Zpower_pos 5 p) (Fexp x)) (Float m e)
 | Z0 => Fcompare radix x (Float m 0)
 end.

Axiom pow_exp :
 forall x y : R, forall n : nat,
 ((pow x n) * (pow y n) = (pow (x * y) n))%R.

Lemma Dcompare_correct :
 forall x : float, forall y : deci,
 match (Dcompare x y) with
 | Lt => (x < y)%R
 | Eq => (float2R x = y)%R
 | Gt => (x > y)%R
 end.
intros x y.
unfold Dcompare.
case y. intros ym ye.
simpl.
induction ye ; unfold deci2R ;
simpl.
rewrite Rmult_1_r.
replace (IZR ym) with (FtoR radix (Float ym 0)).
2: unfold FtoR ; auto with real.
unfold float2R, radix.
CaseEq (Fcompare 2 x (Float ym 0)) ; intro H.
apply Fcompare_Eq with (1 := H).
apply Fcompare_Lt with (1 := H).
apply Fcompare_Gt with (1 := H).
unfold float2R, radix.
assert (H0: (float2R (Float (ym * Zpower_pos 5 p) (Zpos p)) = ym * 10 ^ nat_of_P p)%R).
unfold float2R, radix, FtoR.
simpl.
rewrite mult_IZR.
rewrite Zpower_pos_nat.
rewrite Zpower_nat_Z_powerRZ.
unfold powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite Rmult_assoc.
rewrite pow_exp.
cutrewrite (Zpos 5 * 2 = 10)%R.
trivial.
compute. ring.
CaseEq (Fcompare 2 x (Float (ym * Zpower_pos 5 p) (Zpos p))) ;
 intro H ;
 [ generalize (Fcompare_Eq _ _ H) |
   generalize (Fcompare_Lt _ _ H) |
   generalize (Fcompare_Gt _ _ H) ] ;
 clear H ; rewrite H0 ; trivial.
Admitted.

Definition Dle_fd (x : float) (y : deci) :=
 match (Dcompare x y) with
 | Gt => false
 | _ => true
 end.

Lemma Dle_fd_correct :
 forall x : float, forall y : deci,
 Dle_fd x y = true ->
 (x <= y)%R.
intros x y.
unfold Dle_fd.
generalize (Dcompare_correct x y).
CaseEq (Dcompare x y) ; intros ; auto with real.
discriminate.
Qed.

Definition Dle_df (x : deci) (y : float) :=
 match (Dcompare y x) with
 | Lt => false
 | _ => true
 end.

Lemma Dle_df_correct :
 forall x : deci, forall y : float,
 Dle_df x y = true ->
 (x <= y)%R.
intros x y.
unfold Dle_df.
generalize (Dcompare_correct y x).
CaseEq (Dcompare y x) ; intros ; auto with real.
discriminate.
Qed.

Definition constant2_helper (x : float) (zi : FF) :=
 Fle2 (lower zi) x && Fle2 x (upper zi).

Theorem constant2 :
 forall x : float, forall zi : FF,
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
 constant2_helper (Float x 0) zi = true ->
 BND x zi.
intros x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
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
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 Hx)).
apply Rle_trans with (1 := (proj2 Hx)) (2 := H2).
Qed.

Definition contradiction := forall P, P.

Definition intersect_helper (xf yf : float) (zi : FF) :=
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
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 Hy)).
apply Rle_trans with (1 := (proj2 Hx)) (2 := H2).
Qed.

Theorem intersect_hl :
 forall z : R, forall xf : float, forall yi zi : FF,
 (z <= xf)%R -> BND z yi ->
 intersect_helper xf (lower yi) zi = true ->
 BND z zi.
intros z xf yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 Hy)).
apply Rle_trans with (1 := Hx) (2 := H2).
Qed.

Theorem intersect_hr :
 forall z : R, forall yf : float, forall xi zi : FF,
 BND z xi -> (yf <= z)%R ->
 intersect_helper (upper xi) yf zi = true ->
 BND z zi.
intros z yf xi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
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

Theorem absurd_intersect_hl :
 forall z : R, forall xf : float, forall yi : FF,
 (z <= xf)%R -> BND z yi ->
 Flt2 xf (lower yi) = true ->
 contradiction.
intros z xi yi Hx Hy Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
generalize (Rle_lt_trans _ _ _ Hx H). clear H. intro H.
generalize (Rlt_le_trans _ _ _ H (proj1 Hy)). clear H. intro H.
elim (Rlt_irrefl _ H).
Qed.

Theorem absurd_intersect_hr :
 forall z : R, forall xi : FF, forall yf : float,
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
 forall x z : R, forall xi xi1 zi : FF,
 (BND x xi1 -> BND z zi) ->
 Fle2 (lower xi1) (lower xi) = true ->
 (BND x (makepairF (upper xi1) (upper xi)) -> BND z zi) ->
 BND x xi ->
 BND z zi.
intros x z xi xi1 zi Hx1 Hb Hx2 Hx.
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

Theorem absurd_union :
 forall x : R, forall xi xi1 : FF,
 (BND x xi1 -> contradiction) ->
 Fle2 (lower xi1) (lower xi) = true ->
 (BND x (makepairF (upper xi1) (upper xi)) -> contradiction) ->
 BND x xi ->
 contradiction.
intros x xi xi1 Hx1 Hb Hx2 Hx.
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
 Fle2 (lower zi) (Fopp (upper xi)) &&
 Fle2 (Fopp (lower xi)) (upper zi).

Theorem neg :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 neg_helper xi zi = true ->
 BND (-x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1).
unfold float2R. rewrite Fopp_correct.
apply Ropp_le_contravar with (1 := (proj2 Hx)).
apply Rle_trans with (2 := H2).
unfold float2R. rewrite Fopp_correct.
apply Ropp_le_contravar with (1 := (proj1 Hx)).
Qed.

Definition add_helper (xi yi zi : FF) :=
 Fle2 (lower zi) (Fplus radix (lower xi) (lower yi)) &&
 Fle2 (Fplus radix (upper xi) (upper yi)) (upper zi).

Theorem add :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 add_helper xi yi zi = true ->
 BND (x + y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fplus_correct with (1 := radixNotZero). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fplus_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (IplusR_fun_correct xi yi _ _ Hx Hy). intro H.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 H)).
apply Rle_trans with (1 := (proj2 H)) (2 := H2).
Qed.

Definition sub_helper (xi yi zi : FF) :=
 Fle2 (lower zi) (Fminus radix (lower xi) (upper yi)) &&
 Fle2 (Fminus radix (upper xi) (lower yi)) (upper zi).

Theorem sub :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 sub_helper xi yi zi = true ->
 BND (x - y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite Fminus_correct with (1 := radixNotZero). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fminus_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (IminusR_fun_correct xi yi _ _ Hx Hy). intro H.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := (proj1 H)).
apply Rle_trans with (1 := (proj2 H)) (2 := H2).
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
replace (x - x)%R with R0.
apply contains_zero with (1 := Hb).
rewrite <- Rplus_opp_r with x.
apply refl_equal.
Qed.

Definition mul_pp_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fpos (lower yi) &&
 Fle2 (lower zi) (Fmult (lower xi) (lower yi)) &&
 Fle2 (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_pp :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_pp_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply ImultR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition mul_pn_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fneg (upper yi) &&
 Fle2 (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle2 (Fmult (lower xi) (upper yi)) (upper zi).

Theorem mul_pn :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_pn_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fneg_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply ImultR_pn with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Theorem mul_np :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_pn_helper yi xi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
apply mul_pn with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_nn_helper (xi yi zi : FF) :=
 Fneg (upper xi) &&
 Fneg (upper yi) &&
 Fle2 (lower zi) (Fmult (upper xi) (upper yi)) &&
 Fle2 (Fmult (lower xi) (lower yi)) (upper zi).

Theorem mul_nn :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_nn_helper xi yi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fneg_correct _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply ImultR_nn with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition mul_po_helper (xi yi zi : FF) :=
 Fpos (lower xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle2 (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle2 (Fmult (upper xi) (upper yi)) (upper zi).

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
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold BND, bndR.
apply ImultR_po with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Theorem mul_op :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_po_helper yi xi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
apply mul_po with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_no_helper (xi yi zi : FF) :=
 Fneg (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle2 (lower zi) (Fmult (lower xi) (upper yi)) &&
 Fle2 (Fmult (lower xi) (lower yi)) (upper zi).

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
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fneg0_correct _ H2). clear H2. intro H2.
generalize (Fpos0_correct _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold BND, bndR.
apply ImultR_no with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Theorem mul_on :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 mul_no_helper yi xi zi = true ->
 BND (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
rewrite Rmult_comm.
apply mul_no with (1 := Hy) (2 := Hx) (3 := Hb).
Qed.

Definition mul_oo_helper (xi yi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower yi) && Fpos0 (upper yi) &&
 Fle2 (lower zi) (Fmult (lower xi) (upper yi)) &&
 Fle2 (lower zi) (Fmult (upper xi) (lower yi)) &&
 Fle2 (Fmult (lower xi) (lower yi)) (upper zi) &&
 Fle2 (Fmult (upper xi) (upper yi)) (upper zi).

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
generalize (Fle2_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
generalize (Fle2_correct _ _ H6). rewrite Fmult_correct with (1 := radixNotZero). clear H6. intro H6.
generalize (Fle2_correct _ _ H7). rewrite Fmult_correct with (1 := radixNotZero). clear H7. intro H7.
generalize (Fle2_correct _ _ H8). rewrite Fmult_correct with (1 := radixNotZero). clear H8. intro H8.
unfold BND, bndR.
apply ImultR_oo with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition square_p_helper (xi zi : FF) :=
 Fpos (lower xi) &&
 Fle2 (lower zi) (Fmult (lower xi) (lower xi)) &&
 Fle2 (Fmult (upper xi) (upper xi)) (upper zi).

Theorem square_p :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 square_p_helper xi zi = true ->
 BND (x * x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fmult_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
unfold BND, bndR.
apply ImultR_pp with (lower xi) (upper xi) (lower xi) (upper xi)
 ; auto with real.
Qed.

Definition square_n_helper (xi zi : FF) :=
 Fneg (upper xi) &&
 Fle2 (lower zi) (Fmult (upper xi) (upper xi)) &&
 Fle2 (Fmult (lower xi) (lower xi)) (upper zi).

Theorem square_n :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 square_n_helper xi zi = true ->
 BND (x * x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite Fmult_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
unfold BND, bndR.
apply ImultR_nn with (lower xi) (upper xi) (lower xi) (upper xi)
 ; auto with real.
Qed.

Definition square_o_helper (xi zi : FF) :=
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fneg0 (lower zi) &&
 Fle2 (Fmult (upper xi) (upper xi)) (upper zi) &&
 Fle2 (Fmult (lower xi) (lower xi)) (upper zi).

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
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold BND, bndR.
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

Definition div_pp_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fpos0 (lower xi) &&
 Fle2 (Fmult (upper yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult (lower yi) (upper zi)).

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
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply IdivR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition div_op_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fle2 (Fmult (lower yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult (lower yi) (upper zi)).

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
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold BND, bndR.
apply IdivR_op with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition div_np_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fneg0 (upper xi) &&
 Fle2 (Fmult (lower yi) (lower zi)) (lower xi) &&
 Fle2 (upper xi) (Fmult (upper yi) (upper zi)).

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
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply IdivR_np with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition div_pn_helper (xi yi zi : FF) :=
 Fneg (upper yi) &&
 Fpos0 (lower xi) &&
 Fle2 (upper xi) (Fmult (upper yi) (lower zi)) &&
 Fle2 (Fmult (lower yi) (upper zi)) (lower xi).

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
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply IdivR_pn with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition div_on_helper (xi yi zi : FF) :=
 Fneg (upper yi) &&
 Fneg0 (lower xi) && Fpos0 (upper xi) &&
 Fle2 (upper xi) (Fmult (upper yi) (lower zi)) &&
 Fle2 (Fmult (upper yi) (upper zi)) (lower xi).

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
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
generalize (Fle2_correct _ _ H5). rewrite Fmult_correct with (1 := radixNotZero). clear H5. intro H5.
unfold BND, bndR.
apply IdivR_on with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition div_nn_helper (xi yi zi : FF) :=
 Fneg (upper yi) &&
 Fneg0 (upper xi) &&
 Fle2 (upper xi) (Fmult (lower yi) (lower zi)) &&
 Fle2 (Fmult (upper yi) (upper zi)) (lower xi).

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
generalize (Fle2_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
unfold BND, bndR.
apply IdivR_nn with (lower xi) (upper xi) (lower yi) (upper yi)
 ; auto with real.
Qed.

Definition compose_helper (xi yi zi : FF) :=
 Fle2 (Float (-1) 0) (lower xi) &&
 Fle2 (Float (-1) 0) (lower yi) &&
 Fle2 (lower zi) (Fplus radix (Fplus radix (lower xi) (lower yi))
                               (Fmult (lower xi) (lower yi))) &&
 Fle2 (Fplus radix (Fplus radix (upper xi) (upper yi))
                    (Fmult (upper xi) (upper yi))) (upper zi).

Theorem compose :
 forall x y : R, forall xi yi zi : FF,
 BND x xi -> BND y yi ->
 compose_helper xi yi zi = true ->
 BND ((x + y) + x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
assert (float2R (Float (-1) 0) = -1)%R.
unfold float2R, FtoR. auto with real.
generalize (Fle2_correct _ _ H1). clear H1. rewrite H. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. rewrite H. intro H2.
generalize (Fle2_correct _ _ H3). 
repeat rewrite Fplus_correct with (1 := radixNotZero).
rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle2_correct _ _ H4).
repeat rewrite Fplus_correct with (1 := radixNotZero).
rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
clear H.
replace (x + y + x * y)%R with ((1 + x) * (1 + y) - 1)%R. 2: ring.
assert (H : (1 + lower zi <= (1 + x) * (1 + y) <= 1 + upper zi)%R).
assert (H0 : (0 = 1 + -1)%R). ring.
assert (Hc : forall a b : R, ((1 + a) * (1 + b) = 1 + (a + b + a * b))%R).
intros a b. ring.
assert (Hi : forall a b c : R, (a <= b <= c)%R -> (1 + a <= 1 + b <= 1 + c)%R).
intros a b c H. split.
apply Rplus_le_compat_l with (1 := proj1 H).
apply Rplus_le_compat_l with (1 := proj2 H).
apply ImultR_pp with (1 + lower xi)%R (1 + upper xi)%R (1 + lower yi)%R (1 + upper yi)%R.
rewrite H0. apply Rplus_le_compat_l with (1 := H1).
rewrite H0. apply Rplus_le_compat_l with (1 := H2).
rewrite Hc. apply Rplus_le_compat_l with (1 := H3).
rewrite Hc. apply Rplus_le_compat_l with (1 := H4).
apply Hi with (1 := Hx).
apply Hi with (1 := Hy).
unfold BND, bndR, FF2RR, Rminus. simpl.
assert (H0 : forall a : R, (a = (1 + a) + -1)%R).
intros a. ring.
split.
rewrite (H0 (lower zi)). apply Rplus_le_compat_r with (1 := proj1 H).
rewrite (H0 (upper zi)). apply Rplus_le_compat_r with (1 := proj2 H).
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
 Fle2 (lower zi) (Fopp (upper xi)) &&
 Fle2 (upper xi) (upper zi).

Theorem invert_abs :
 forall x : R, forall xi zi : FF,
 BND (Rabs x) xi ->
 invert_abs_helper xi zi = true ->
 BND x zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1).
unfold float2R. rewrite Fopp_correct.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (2 := proj2 Hx).
pattern x at 2 ; rewrite <- Ropp_involutive.
rewrite Rabs_Ropp.
apply Rabs_idem.
apply Rle_trans with (2 := H2).
apply Rle_trans with (1 := Rabs_idem x) (2 := proj2 Hx).
Qed.

Definition abs_p_helper (xi zi : FF) :=
 Fpos0 (lower xi) &&
 Fle2 (lower zi) (lower xi) &&
 Fle2 (upper xi) (upper zi).

Theorem abs_p :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 abs_p_helper xi zi = true ->
 BND (Rabs x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H2).
apply Rle_trans with (1 := proj1 Hx) (2 := Rabs_idem x).
apply Rle_trans with (2 := H3).
apply Rle_trans with (2 := proj2 Hx).
apply Req_le.
apply Rabs_pos_eq.
apply Rle_trans with (1 := H1) (2 := proj1 Hx).
Qed.

Definition abs_o_helper (xi zi : FF) :=
 Fneg0 (lower zi) &&
 Fle2 (upper xi) (upper zi) &&
 Fle2 (Fopp (lower xi)) (upper zi).

Theorem abs_o :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 abs_o_helper xi zi = true ->
 BND (Rabs x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1) (2 := Rabs_pos x).
unfold Rabs. case Rcase_abs ; intro H.
unfold float2R in H3. rewrite Fopp_correct in H3.
apply Rle_trans with (2 := H3).
apply Ropp_le_contravar with (1 := proj1 Hx).
apply Rle_trans with (1 := proj2 Hx) (2 := H2).
Qed.

Definition abs_n_helper (xi zi : FF) :=
 Fneg0 (upper xi) &&
 Fle2 (lower zi) (Fopp (upper xi)) &&
 Fle2 (Fopp (lower xi)) (upper zi).

Theorem abs_n :
 forall x : R, forall xi zi : FF,
 BND x xi ->
 abs_n_helper xi zi = true ->
 BND (Rabs x) zi.
intros x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fneg0_correct _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). unfold float2R. rewrite Fopp_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). unfold float2R. rewrite Fopp_correct. clear H3. intro H3.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H2).
rewrite <- (Rabs_Ropp x).
apply Rle_trans with (2 := Rabs_idem (-x)).
apply Ropp_le_contravar with (1 := proj2 Hx).
apply Rle_trans with (2 := H3).
apply Rle_trans with (Ropp x).
apply Req_le.
apply Rabs_left1.
apply Rle_trans with (1 := proj2 Hx) (2 := H1).
apply Ropp_le_contravar with (1 := proj1 Hx).
Qed.

End Gappa_pred_bnd.
