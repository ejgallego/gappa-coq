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

Lemma Eabsolute_hulp :
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

Definition hulp1 := Float 1 (-precision)%Z.

Lemma hulp1_lt_1 : (hulp1 < 1)%R.
unfold hulp1, float2R, FtoR.
simpl.
rewrite Rmult_1_l.
pattern 1%R at 3; rewrite <- (powerRZ_O 2).
apply Rlt_powerRZ.
apply Rlt_plus_1.
auto with zarith.
Qed.

Axiom plouf : forall P : Prop, P.

Lemma Rabsolute_hulp :
 forall xa : cFloat, forall xr : R,
 Rounded xr xa -> Fnormal radix bound (value xa) ->
 ErelativeR (makepairR (-hulp1) hulp1) xr xa.
intros xa xr Hr Hn.
unfold ErelativeR.
split.
simpl.
apply Ropp_lt_contravar.
exact hulp1_lt_1.
assert (float2R (value xa) <> 0)%R.
intro Hz.
elim (FnormalNotZero _ _ (value xa) Hn).
exact (is_Fzero_rep2 _ radixMoreThanOne _ Hz).
split.
exact H.
unfold IintR, Iplus1R.
simpl.
cut (-hulp1 <= xr / xa - 1 <= hulp1)%R. intros (H1, H2).
replace (xr / xa)%R with (1 + (xr / xa - 1))%R.
split; apply Rplus_le_compat_l.
exact H1.
exact H2.
ring.
apply Rabs_ineq.
replace (xr / xa - 1)%R with ((xr - xa) * /xa)%R.
2: field; exact H.
rewrite Rabs_mult.
rewrite (Rabs_Rinv xa H).
apply Rmult_le_reg_l with (Rabs xa).
exact (Rabs_pos_lt _ H).
replace (Rabs xa * (Rabs (xr - xa) * / Rabs xa))%R with (Rabs (xr - xa))%R.
apply Rle_trans with (RError xa).
exact (RError_correct _ _ Hr).
unfold RError, hulp1, cFloat2R, float2R, FtoR.
simpl.
repeat rewrite Rmult_1_l.
apply Rmult_le_reg_l with 2%R.
exact Rlt2.
apply Rle_trans with (Zpos (vNum bound) * powerRZ 2 (Fexp (value xa)) * powerRZ 2 (-precision))%R.
rewrite pGivesBound.
replace radix with (Z_of_nat 2%nat). 2: apply refl_equal.
rewrite Zpower_nat_powerRZ.
pattern 2%R at 1; replace 2%R with (powerRZ 2 1). 2: auto with real.
repeat rewrite <- powerRZ_add; auto with real.
apply Rle_powerRZ.
auto with real.
omega.
repeat rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
exact (powerRZ_le _ _ Rlt2).
rewrite Rabs_mult.
rewrite (Rabs_right (powerRZ 2 (Fexp (value xa)))).
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
exact (powerRZ_le _ _ Rlt2).



rewrite <- Rmult_assoc.

rewrite Rabs_mult.
rewrite Rmult_assoc.
apply Rmult_le_compat.
auto with real.
auto with real.
case (total_order_T (value xa) 0); intro H0.
case H0; clear H0; intro H0.
2: contradiction.
apply plouf.
apply plouf.
rewrite Rmult_1_l.
rewrite Rabs_right.
rewrite <- powerRZ_add.
2: auto with real.
apply Rle_powerRZ.
auto with real.
unfold Zminus.
apply Zplus_le_compat_l.
auto with zarith.

assert (forall a b : R, (b <> 0)%R -> (a = b * (a * /b))%R).
intros a b Hb.
field.
exact Hb.
apply H0.
apply Rgt_not_eq.
exact (Rabs_pos_lt _ H).
Qed.

End IA_float.
