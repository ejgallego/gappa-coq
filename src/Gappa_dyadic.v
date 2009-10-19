Require Import ZArith.
Require Import Reals.
Require Import Gappa_integer.
Require Import Gappa_definitions.

Section Gappa_dyadic.

Lemma float2_zero :
 forall e : Z, Float2 0 e = R0 :>R.
intro e.
unfold float2R.
rewrite F2R_split.
rewrite Rmult_0_l.
apply refl_equal.
Qed.

Definition Fopp2 (x : float2) :=
 Float2 (- Fnum x) (Fexp x).

Lemma Fopp2_correct :
 forall x : float2,
 Fopp2 x = (- x)%R :>R.
intros x.
unfold float2R, Fopp2.
do 2 rewrite F2R_split.
simpl.
rewrite opp_Z2R.
apply Ropp_mult_distr_l_reverse.
Qed.

Definition Fmult2 (x y : float2) :=
 Float2 (Fnum x * Fnum y) (Fexp x + Fexp y).

Definition Fmult2_correct :
 forall x y : float2,
 Fmult2 x y = (x * y)%R :>R.
intros x y.
unfold float2R, Fmult2.
do 3 rewrite F2R_split.
simpl.
rewrite powerRZ_add.
rewrite mult_Z2R.
repeat rewrite Rmult_assoc.
ring.
change 2%R with (INR 2).
auto with real.
Qed.

Definition shl (m : Z) (d : positive) :=
 match m with
 | Z0 => Z0
 | Zpos p => Zpos (shift_pos d p)
 | Zneg p => Zneg (shift_pos d p)
 end.

Lemma float2_shl_correct :
 forall m e : Z, forall d : positive,
 Float2 (shl m d) (e - Zpos d) = Float2 m e :>R.
assert (forall p d : positive, forall e : Z,
        Float2 (shl (Zpos p) d) (e - Zpos d) = Float2 (Zpos p) e :>R).
intros p d e.
unfold float2R, shl.
rewrite shift_pos_correct.
simpl.
rewrite Zpower_pos_nat.
change 2%Z with (Z_of_nat 2).
do 2 rewrite F2R_split.
rewrite mult_Z2R.
rewrite Z2R_IZR.
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
rewrite <- powerRZ_add. 2: auto with real.
replace (e - Zpos d + Zpos d)%Z with e by ring.
apply Rmult_comm.
intros m e d.
induction m.
2: apply H.
unfold shl.
repeat rewrite float2_zero.
apply refl_equal.
unfold shl.
cutrewrite (Float2 (Zneg (shift_pos d p)) (e - Zpos d) =
            - Float2 (shl (Zpos p) d) (e - Zpos d) :>R)%R.
rewrite H.
rewrite <- Fopp2_correct.
apply refl_equal.
rewrite <- Fopp2_correct.
apply refl_equal.
Qed.

Definition Fshift2 (x y : float2) :=
 match (Fexp x - Fexp y)%Z with
 | Zpos p => (shl (Fnum x) p, Fnum y, Fexp y)
 | Zneg p => (Fnum x, shl (Fnum y) p, Fexp x)
 | Z0 => (Fnum x, Fnum y, Fexp x)
 end.

Ltac caseEq f := generalize (refl_equal f) ; pattern f at -1 ; case f.

Lemma Fshift2_correct :
 forall x y : float2,
 match Fshift2 x y with
 | (mx, my, e) => Float2 mx e = x :>R /\ Float2 my e = y :>R
 end.
intros x y.
unfold Fshift2.
caseEq (Fexp x - Fexp y)%Z ; intros ; split ; try apply refl_equal.
replace (Fexp x) with (Fexp y).
apply refl_equal.
auto with zarith.
replace (Fexp y) with (Fexp x - Zpos p)%Z.
induction x.
apply float2_shl_correct.
omega.
replace (Fexp x) with (Fexp y - Zpos p)%Z.
induction y.
apply float2_shl_correct.
replace (Zpos p) with (-Zneg p)%Z.
omega.
apply refl_equal.
Qed.

Definition Fplus2 (x y : float2) :=
 match Fshift2 x y with
 | (mx, my, e) => Float2 (mx + my) e
 end.

Lemma Fplus2_correct :
 forall x y : float2,
 Fplus2 x y = (x + y)%R :>R.
intros x y.
unfold Fplus2.
generalize (Fshift2_correct x y).
case (Fshift2 x y).
intros (mx,my) e.
unfold float2R.
simpl.
intros (Hx, Hy).
rewrite F2R_split.
rewrite plus_Z2R.
rewrite Rmult_plus_distr_r.
do 2 rewrite <- F2R_split.
rewrite Hx.
rewrite Hy.
apply refl_equal.
Qed.

Definition Fminus2 (x y : float2) :=
 match Fshift2 x y with
 | (mx, my, e) => Float2 (mx - my) e
 end.

Lemma Fminus2_correct :
 forall x y : float2,
 Fminus2 x y = (x - y)%R :>R.
intros x y.
unfold Fminus2.
generalize (Fshift2_correct x y).
case (Fshift2 x y).
intros (mx,my) e.
unfold float2R.
simpl.
intros (Hx, Hy).
rewrite F2R_split.
rewrite minus_Z2R.
assert (forall a b c : R, (a - b) * c = a * c - b * c)%R by (intros ; ring).
rewrite H.
do 2 rewrite <- F2R_split.
rewrite Hx.
rewrite Hy.
apply refl_equal.
Qed.

Definition Fcomp2 (x y : float2) :=
 match Fshift2 x y with
 | (mx, my, _) => (mx ?= my)%Z
 end.

Lemma Fcomp2_Eq :
 forall x y : float2,
 Fcomp2 x y = Eq ->
 x = y :>R.
intros x y.
generalize (Fshift2_correct x y).
unfold Fcomp2.
case (Fshift2 x y).
intros (mx, my) e (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
unfold float2R. simpl.
replace my with mx.
exact (refl_equal _).
apply Zcompare_Eq_eq.
exact Hb.
Qed.

Lemma power_radix_pos :
  forall r e, (0 < powerRZ (P2R r) e)%R.
intros.
apply powerRZ_lt.
change (P2R r) with (Z2R (Zpos r)).
apply (Z2R_lt 0).
exact (refl_equal _).
Qed.

Lemma Fcomp2_Lt :
 forall x y : float2,
 Fcomp2 x y = Lt ->
 (x < y)%R.
intros x y.
generalize (Fshift2_correct x y).
unfold Fcomp2.
case (Fshift2 x y).
intros (mx, my) e (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
unfold float2R. simpl.
do 2 rewrite F2R_split.
apply Rmult_lt_compat_r.
apply power_radix_pos.
apply Z2R_lt.
exact Hb.
Qed.

Lemma Fcomp2_Gt :
 forall x y : float2,
 Fcomp2 x y = Gt ->
 (x > y)%R.
intros x y.
generalize (Fshift2_correct x y).
unfold Fcomp2.
case (Fshift2 x y).
intros (mx, my) e (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
unfold float2R. simpl.
unfold Rgt.
do 2 rewrite F2R_split.
apply Rmult_lt_compat_r.
apply power_radix_pos.
apply Z2R_lt.
apply Zgt_lt.
exact Hb.
Qed.

Definition Feq2 (x y : float2) :=
 match Fcomp2 x y with
 | Eq => true
 | _ => false
 end.

Lemma Feq2_correct :
 forall x y : float2,
 Feq2 x y = true -> x = y :>R.
intros x y Hb.
apply Fcomp2_Eq.
unfold Feq2 in Hb.
generalize Hb. clear Hb.
case (Fcomp2 x y) ; intro H ; try discriminate H.
apply refl_equal.
Qed.

Definition Flt2 (x y : float2) :=
 match Fcomp2 x y with
 | Lt => true
 | _ => false
 end.

Lemma Flt2_correct :
 forall x y : float2,
 Flt2 x y = true -> (x < y)%R.
intros x y Hb.
apply Fcomp2_Lt.
unfold Flt2 in Hb.
generalize Hb. clear Hb.
case (Fcomp2 x y) ; intro H ; try discriminate H.
apply refl_equal.
Qed.

Definition Fle2 (x y : float2) :=
 match Fcomp2 x y with
 | Gt => false
 | _ => true
 end.

Lemma Fle2_correct :
 forall x y : float2,
 Fle2 x y = true -> (x <= y)%R.
intros x y.
generalize (Fshift2_correct x y).
unfold Fle2, Fcomp2.
case (Fshift2 x y).
intros (mx, my) e (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
unfold float2R. simpl.
do 2 rewrite F2R_split.
apply Rmult_le_compat_r.
apply Rlt_le.
apply power_radix_pos.
apply Z2R_le.
apply Znot_gt_le.
unfold Zgt.
intro H.
unfold Fle2, Fcomp2, Fshift2 in Hb.
rewrite H in Hb.
discriminate Hb.
Qed.

Inductive Fle2_prop (x y : float2) : bool -> Prop :=
  | Fle2_true : (x <= y)%R -> Fle2_prop x y true
  | Fle2_false : (y < x)%R -> Fle2_prop x y false.

Lemma Fle2_spec :
  forall x y, Fle2_prop x y (Fle2 x y).
Proof.
intros x y.
case_eq (Fle2 x y) ; intros H.
apply Fle2_true.
apply Fle2_correct.
exact H.
generalize H. clear H.
unfold Fle2.
case_eq (Fcomp2 x y) ; try (intros ; discriminate).
intros H _.
apply Fle2_false.
apply Fcomp2_Gt.
exact H.
Qed.

Definition Fis0 (x : float2) :=
 match (Fnum x) with
   Z0 => true
 | _ => false
 end.

Lemma Fis0_correct :
 forall x : float2,
 Fis0 x = true -> x = R0 :>R.
intros x.
unfold Fis0.
induction x.
induction Fnum ; intro H0 ; try discriminate.
apply float2_zero.
Qed.

Definition Fpos (x : float2) :=
 match (Fnum x) with
   Zpos _ => true
 | _ => false
 end.

Lemma Fpos_correct :
 forall x : float2,
 Fpos x = true -> (0 < x)%R.
intros x H.
unfold float2R.
rewrite F2R_split.
apply Rmult_lt_0_compat.
generalize H. clear H.
unfold IZR, Fpos.
induction (Fnum x) ; intro H0 ; try discriminate.
apply (Z2R_lt 0).
exact (refl_equal _).
apply power_radix_pos.
Qed.

Definition Fneg (x : float2) :=
 match (Fnum x) with
   Zneg _ => true
 | _ => false
 end.

Lemma Fneg_correct :
 forall x : float2,
 Fneg x = true -> (x < 0)%R.
intros x H.
unfold float2R.
rewrite F2R_split.
rewrite <- (Ropp_involutive (Z2R (Fnum x))).
rewrite <- opp_Z2R.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_gt_0_contravar.
unfold Rgt.
apply Rmult_lt_0_compat.
apply (Z2R_lt 0).
unfold Fneg in H.
induction (Fnum x) ; try discriminate.
exact (refl_equal _).
apply power_radix_pos.
Qed.

Definition Fpos0 (x : float2) :=
 match (Fnum x) with
   Zneg _ => false
 | _ => true
 end.

Lemma Fpos0_correct :
 forall x : float2,
 Fpos0 x = true -> (0 <= x)%R.
intros x H.
unfold float2R.
rewrite F2R_split.
apply Rmult_le_pos.
apply (Z2R_le 0).
unfold Fpos0 in H.
induction (Fnum x) ; try discriminate.
apply Rlt_le.
apply power_radix_pos.
Qed.

Definition Fneg0 (x : float2) :=
 match (Fnum x) with
   Zpos _ => false
 | _ => true
 end.

Lemma Fneg0_correct :
 forall x : float2,
 Fneg0 x = true -> (x <= 0)%R.
intros x H.
unfold float2R.
rewrite F2R_split.
rewrite <- (Ropp_involutive (Z2R (Fnum x))).
rewrite <- opp_Z2R.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply Rmult_le_pos.
apply (Z2R_le 0).
unfold Fneg0 in H.
induction (Fnum x) ; try discriminate.
apply Rlt_le.
apply power_radix_pos.
Qed.

Definition Flt2_m1 f :=
  Flt2 (Float2 (-1) 0) f.

Lemma Flt2_m1_correct :
  forall f,
  Flt2_m1 f = true ->
  (-1 < f)%R.
Proof.
intros f Hb.
exact (Flt2_correct _ _ Hb).
Qed.

End Gappa_dyadic.
