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

End IA_comput.
