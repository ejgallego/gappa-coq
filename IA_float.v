Add LoadPath "Float".
Require Export AllFloat.
Require Export IA_real.
Require Export IA_error.
Require Export ZArith.

Section IA_float.

Definition radix := 2%Z.

Definition radixMoreThanOne := TwoMoreThanOne.
Lemma radixNotZero: (0 < radix)%Z.
auto with zarith.
Qed.

Variable precision : nat.
Hypothesis precisionMoreThanOne : lt (1) precision.
Lemma precisionNotZero : ~(precision = (0)).
auto with zarith.
Qed.

Variable bExp : nat.
Definition bNum := iter_nat precision positive xO xH.
Definition bound := Bound bNum bExp.

Lemma pGivesBound : Zpos (vNum bound) = Zpower_nat radix precision.
unfold vNum, bound, bNum, Zpower_nat.
elim precision. trivial.
intros n H.
Opaque Zmult.
simpl.
rewrite <- H.
Transparent Zmult.
simpl.
apply refl_equal.
Qed.

Record cFloat : Set := CFloat {
  value : float;
  cFloat_canonic : Fcanonic radix bound value
}.
Coercion Local cFloat2R (x : cFloat) := FtoR radix (value x).
Coercion Local float2R := FtoR radix.

Definition Rounded (xr : R) (xa : cFloat) :=
 EvenClosest bound radix precision xr (value xa).

Definition RError (x : cFloat) := Float 1 ((Fexp (value x)) - 1)%Z.

Lemma RError_correct :
 forall xa : cFloat, forall xr : R,
 Rounded xr xa ->
 (Rabs (xr - xa) <= RError xa)%R.
intros xa xr Hr.
apply (Rmult_le_reg_l 2 (Rabs (xr - xa))%R (RError xa) Rlt2).
assert (2 * (RError xa) = (Fulp bound radix precision (value xa)))%R.
unfold RError, Fulp, cFloat2R, float2R, FtoR. simpl.
unfold Zminus. simpl.
assert (2 <> 0)%R.
apply Rlt_dichotomy_converse. right. exact Rlt2.
rewrite powerRZ_add. 2: exact H.
simpl.
replace (2*(1*((powerRZ 2 (Fexp (value xa)))*/(2*1))))%R with (powerRZ 2 (Fexp (value xa))).
rewrite (FcanonicFnormalizeEq _ radixMoreThanOne _ _ precisionNotZero pGivesBound).
apply refl_equal.
exact (cFloat_canonic xa).
field.
ring (2 * 1)%R.
exact H.
rewrite H.
unfold cFloat2R.
apply (ClosestUlp _ _ _ radixMoreThanOne precisionMoreThanOne pGivesBound).
unfold Rounded, EvenClosest in Hr.
exact (proj1 Hr).
Qed.

Lemma RError_range_correct_aux:
 forall x y : cFloat,
 (Rabs x <= Rabs y)%R ->
 (RError x <= RError y)%R.
intros x y H.
unfold RError, float2R, FtoR.
simpl.
apply Rmult_le_compat_l. auto with real.
apply Rle_powerRZ. auto with real.
unfold Zminus.
apply Zplus_le_compat_r.
exact (Fcanonic_Rle_Zle _ radixMoreThanOne _ _ precisionNotZero pGivesBound
 _ _ (cFloat_canonic x) (cFloat_canonic y) H).
Qed.

Record FF: Set := makepairF { lower : cFloat ; upper : cFloat }.
Coercion Local FF2RR := fun x : FF => makepairR (lower x) (upper x).
Definition IintF (xi : FF) (x : cFloat) := IintR xi x.

Lemma RError_range_correct :
 forall xi : FF, forall x : cFloat, forall e : float,
 IintF xi x ->
 (RError (lower xi) <= e)%R -> (RError (upper xi) <= e)%R ->
 (RError x <= e)%R.
intros xi x e H Hle Hue.
case (IintR_abs _ _ H); clear H; intro H; simpl in H.
apply Rle_trans with (RError (lower xi)). 2: exact Hle.
exact (RError_range_correct_aux _ _ H).
apply Rle_trans with (RError (upper xi)). 2: exact Hue.
exact (RError_range_correct_aux _ _ H).
Qed.

Definition cFloat_error (xi : FF) :=
 Float 1 ((Zmax (Fexp (value (lower xi))) (Fexp (value (upper xi)))) - 1)%Z.

Lemma float_le_exp :
 forall a b : Z, (a <= b)%Z ->
 (Float 1 a <= Float 1 b)%R.
intros a b H.
unfold float2R, FtoR.
simpl.
apply Rmult_le_compat_l.
auto with real.
apply Rle_powerRZ.
auto with real.
exact H.
Qed.

Lemma cFloat_error_RError :
 forall xi : FF, forall x : cFloat,
 IintF xi x ->
 (RError x <= cFloat_error xi)%R.
intros xi x H.
apply (RError_range_correct _ _ (cFloat_error xi) H); unfold cFloat_error, RError.
apply float_le_exp. unfold Zminus. apply Zplus_le_compat_r. apply ZmaxLe1.
apply float_le_exp. unfold Zminus. apply Zplus_le_compat_r. apply ZmaxLe2.
Qed.

Lemma Rabs_ineq :
 forall a b : R, (Rabs a <= b)%R ->
 (-b <= a <= b)%R.
intros a b H.
assert (0 <= b)%R.
apply Rle_trans with (Rabs a)%R.
apply Rabs_pos.
exact H.
elim (Rcase_abs a); intro H1; split.
replace a with (-Rabs a)%R.
exact (Ropp_le_contravar _ _ H).
pattern a at 2; rewrite <- Ropp_involutive.
apply Ropp_eq_compat.
exact (Rabs_left _ H1).
apply Rlt_le.
exact (Rlt_le_trans _ _ _ H1 H0).
apply Rle_trans with 0%R.
rewrite <- Ropp_0.
exact (Ropp_le_contravar _ _ H0).
exact (Rge_le _ _ H1).
exact (Rle_trans _ _ _ (RRle_abs _) H).
Qed.

Lemma Eabsolute_RError :
 forall xi : FF, forall xa : cFloat, forall xr : R,
 Rounded xr xa -> IintF xi xa ->
 let e := cFloat_error xi in
 EabsoluteR (makepairR (-e) e) xr xa.
intros xi xa xr Hr Hi e.
unfold EabsoluteR, IintR. simpl.
assert (Rabs (xr - xa) <= e)%R.
apply Rle_trans with (RError xa).
apply (RError_correct _ _ Hr).
apply (cFloat_error_RError _ _ Hi).
exact (Rabs_ineq _ _ H).
Qed.

End IA_float.
