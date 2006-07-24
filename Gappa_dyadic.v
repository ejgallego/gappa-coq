Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.

Section Gappa_dyadic.

Definition Fopp2 (x : float2) :=
 Float2 (- Fnum x) (Fexp x).

Lemma Fopp2_correct :
 forall x : float2,
 Fopp2 x = (- x)%R :>R.
intros x.
unfold float2R, Fopp2.
simpl.
rewrite Ropp_Ropp_IZR.
auto with real.
Qed.

Definition Fmult2 (x y : float2) :=
 Float2 (Fnum x * Fnum y) (Fexp x + Fexp y).

Definition Fmult2_correct :
 forall x y : float2,
 Fmult2 x y = (x * y)%R :>R.
intros x y.
unfold float2R, Fmult2.
simpl.
rewrite powerRZ_add.
rewrite mult_IZR.
repeat rewrite Rmult_assoc.
repeat rewrite (Rmult_comm (IZR (Fnum y))).
repeat rewrite <- Rmult_assoc.
apply refl_equal.
replace 2%R with (INR 2). 2: apply refl_equal.
auto with real.
Qed.

Definition shl (m : Z) (d : positive) :=
 match m with
 | Z0 => Z0
 | Zpos p => Zpos (shift_pos d p)
 | Zneg p => Zneg (shift_pos d p)
 end.

Lemma float2_shl_correct :
 forall f : float2, forall d : positive,
 Float2 (shl (Fnum f) d) (Fexp f - Zpos d) = f :>R.
assert (forall p d : positive, forall e : Z,
        Float2 (shl (Zpos p) d) (e - Zpos d) = Float2 (Zpos p) e :>R).
intros p d e.
unfold float2R, shl.
rewrite shift_pos_correct.
simpl.
rewrite Zpower_pos_nat.
replace 2%Z with (Z_of_nat 2). 2: apply refl_equal.
rewrite mult_IZR.
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
rewrite <- powerRZ_add. 2: auto with real.
ring (e - Zpos d + Zpos d)%Z.
rewrite Rmult_comm.
auto with real.
intros f d.
replace f with (Float2 (Fnum f) (Fexp f)).
2: induction f ; apply refl_equal.
simpl.
case (Fnum f) ; intros. 2: apply H.
unfold float2R, shl.
simpl.
repeat rewrite Rmult_0_l.
apply refl_equal.
unfold shl.
cutrewrite (Float2 (Zneg (shift_pos d p)) (Fexp f - Zpos d) =
            - Float2 (shl (Zpos p) d) (Fexp f - Zpos d) :>R)%R.
rewrite H.
unfold float2R.
simpl.
auto with real.
unfold float2R.
unfold shl.
simpl.
auto with real.
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
apply float2_shl_correct.
auto with zarith.
replace (Fexp x) with (Fexp y - Zpos p)%Z.
apply float2_shl_correct.
replace (Zpos p) with (-Zneg p)%Z.
auto with zarith.
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
intros p e. case p. clear p.
intros mx my.
unfold float2R.
simpl.
intros (Hx, Hy).
rewrite plus_IZR.
rewrite Rmult_plus_distr_r.
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
intros p e. case p. clear p.
intros mx my.
unfold float2R.
simpl.
intros (Hx, Hy).
rewrite <- Z_R_minus.
assert (forall a b c : R, (a - b) * c = a * c - b * c)%R.
intros. ring.
rewrite H.
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
intros p e. case p. clear p.
intros mx my (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
clear Hx Hy.
unfold float2R. simpl.
ring. apply Rmult_eq_compat_l.
apply IZR_eq.
apply Zcompare_Eq_eq.
exact Hb.
Qed.

Lemma Fcomp2_Lt :
 forall x y : float2,
 Fcomp2 x y = Lt ->
 (x < y)%R.
intros x y.
generalize (Fshift2_correct x y).
unfold Fcomp2.
case (Fshift2 x y).
intros p e. case p. clear p.
intros mx my (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
clear Hx Hy.
unfold float2R. simpl.
apply Rmult_lt_compat_r.
auto with real.
apply IZR_lt.
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
intros p e. case p. clear p.
intros mx my (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
clear Hx Hy.
unfold float2R. simpl.
unfold Rgt. apply Rmult_lt_compat_r.
auto with real.
apply IZR_lt.
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
intros p e. case p. clear p.
intros mx my (Hx, Hy) Hb.
rewrite <- Hx.
rewrite <- Hy.
clear Hx Hy.
unfold float2R. simpl.
apply Rmult_le_compat_r.
auto with real.
apply IZR_le.
apply Znot_gt_le.
unfold Zgt.
intro H.
unfold Fle2, Fcomp2, Fshift2 in Hb.
rewrite H in Hb.
discriminate Hb.
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
unfold float2R, Fis0.
induction (Fnum x) ; intro H0 ; try discriminate.
apply Rmult_0_l.
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
apply Rmult_lt_0_compat.
2: auto with real.
generalize H. clear H.
unfold IZR, Fpos.
induction (Fnum x) ; intro H0 ; try discriminate.
apply INR_pos.
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
apply Rmult_le_pos.
2: auto with real.
generalize H. clear H.
unfold IZR, Fpos0.
induction (Fnum x) ; intro H0 ; try discriminate
 ; auto with real.
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

End Gappa_dyadic.
