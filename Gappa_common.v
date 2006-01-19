Require Import AllFloat.
Require Export Gappa_real.

Section Gappa_comp_common.

Definition radix := 2%Z.

Definition radixMoreThanOne := TwoMoreThanOne.
Lemma radixNotZero: (0 < radix)%Z.
auto with zarith.
Qed.

Coercion float2R := FtoR radix.
Record FF: Set := makepairF { lower : float ; upper : float }.
Coercion FF2RR := fun x : FF => makepairR (lower x) (upper x).

Definition BND (x : R) (xi : FF) :=
 bndR x xi.
Definition ABS (x : R) (xi : FF) :=
 (0 <= lower xi)%R /\ bndR (Rabs x) xi.
Definition FIX (x : R) (n : Z) :=
 exists f : float, float2R f = x /\ (n <= Fexp f)%Z.
Definition FLT (x : R) (n : positive) :=
 exists f : float, float2R f = x /\ (Zabs (Fnum f) < Zpower_pos radix n)%Z.

Definition Fle2 (x y : float) := Fle_bool radix x y.

Lemma Fle2_correct :
 forall x y : float,
 Fle2 x y = true -> (x <= y)%R.
intros x y H.
apply (Fle_bool_correct_t radix radixMoreThanOne).
exact H.
Qed.

Definition Feq2 (x y : float) := Feq_bool radix x y.

Lemma Feq2_correct :
 forall x y : float,
 Feq2 x y = true -> (float2R x = y).
intros x y H.
apply (Feq_bool_correct_t radix radixMoreThanOne).
exact H.
Qed.

Definition Flt2 (x y : float) := Flt_bool radix x y.

Lemma Flt2_correct :
 forall x y : float,
 Flt2 x y = true -> (x < y)%R.
intros x y H.
apply (Flt_bool_correct_t radix radixMoreThanOne).
exact H.
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

Definition abs_not_zero (zi : FF) := Fpos (lower zi).

Lemma abs_not_zero_correct :
 forall z : R, forall zi : FF,
 ABS z zi ->
 abs_not_zero zi = true ->
 (z <> 0)%R.
intros z zi Hz Hb. 
generalize (Fpos_correct _ Hb). clear Hb. intro H.
case (Rcase_abs z) ; intro.
apply Rlt_not_eq with (1 := r).
rewrite <- (Rabs_right z r).
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H) (2 := proj1 (proj2 Hz)).
Qed.

End Gappa_comp_common.
