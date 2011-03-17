Require Import ZArith.
Require Import Reals.
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.
Require Import Fcalc_ops.
Require Import Gappa_definitions.

Section Gappa_dyadic.

Lemma float2_zero :
  forall e : Z, Float2 0 e = R0 :>R.
Proof.
intro e.
apply F2R_0.
Qed.

Definition Fopp2 (x : float2) :=
 Float2 (- Fnum x) (Fexp x).

Lemma Fopp2_correct :
  forall x : float2,
  Fopp2 x = (- x)%R :>R.
Proof.
intros x.
unfold float2R, Fopp2. simpl.
apply sym_eq.
apply opp_F2R.
Qed.

Definition Fmult2 (x y : float2) :=
 Float2 (Fnum x * Fnum y) (Fexp x + Fexp y).

Definition Fmult2_correct :
  forall x y : float2,
  Fmult2 x y = (x * y)%R :>R.
Proof.
intros (mx, ex) (my, ey).
exact (mult_F2R radix2 (Float radix2 mx ex) (Float radix2 my ey)).
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
Proof.
intros m e d.
replace (shl m d) with (m * Zpower_pos 2 d)%Z.
unfold float2R.
rewrite (F2R_change_exp _ (e - Zpos d) _ e).
simpl.
now replace (e - (e - Zpos d))%Z with (Zpos d) by ring.
generalize (Zgt_pos_0 d).
omega.
rewrite Zmult_comm.
destruct m as [|m|m] ; simpl.
apply Zmult_0_r.
now rewrite shift_pos_correct.
change (Zneg (shift_pos d m)) with (- Zpos (shift_pos d m))%Z.
rewrite shift_pos_correct.
now rewrite Zopp_mult_distr_r.
Qed.

Definition Fshift2 (x y : float2) :=
 match (Fexp x - Fexp y)%Z with
 | Zpos p => (shl (Fnum x) p, Fnum y, Fexp y)
 | Zneg p => (Fnum x, shl (Fnum y) p, Fexp x)
 | Z0 => (Fnum x, Fnum y, Fexp x)
 end.

Lemma Fshift2_correct :
  forall x y : float2,
  match Fshift2 x y with
  | (mx, my, e) => Float2 mx e = x :>R /\ Float2 my e = y :>R
  end.
Proof.
intros (mx, ex) (my, ey).
unfold Fshift2. simpl.
assert (ex = ex - ey + ey)%Z by ring.
pattern ex at - 1 ; rewrite H.
destruct (ex - ey)%Z as [|d|d] ; repeat split.
rewrite <- (float2_shl_correct mx _ d).
now ring_simplify (Zpos d + ey - Zpos d)%Z.
rewrite Zplus_comm.
apply float2_shl_correct.
Qed.

Definition Fplus2 (x y : float2) :=
 match Fshift2 x y with
 | (mx, my, e) => Float2 (mx + my) e
 end.

Lemma Fplus2_correct :
  forall x y : float2,
  Fplus2 x y = (x + y)%R :>R.
Proof.
intros x y.
unfold Fplus2.
generalize (Fshift2_correct x y).
destruct (Fshift2 x y) as ((mx, my), e).
intros (Hx, Hy).
rewrite <- Hx, <- Hy.
unfold float2R, F2R. simpl.
rewrite Z2R_plus.
apply Rmult_plus_distr_r.
Qed.

Definition Fminus2 (x y : float2) :=
 match Fshift2 x y with
 | (mx, my, e) => Float2 (mx - my) e
 end.

Lemma Fminus2_correct :
  forall x y : float2,
  Fminus2 x y = (x - y)%R :>R.
Proof.
intros x y.
unfold Fminus2.
generalize (Fshift2_correct x y).
destruct (Fshift2 x y) as ((mx, my), e).
intros (Hx, Hy).
rewrite <- Hx, <- Hy.
unfold float2R, F2R. simpl.
rewrite Z2R_minus.
apply Rmult_minus_distr_r.
Qed.

Definition Fcomp2 (x y : float2) :=
 match Fshift2 x y with
 | (mx, my, _) => (mx ?= my)%Z
 end.

Lemma Fcomp2_correct :
  forall x y : float2,
  Fcomp2 x y = Rcompare x y.
Proof.
intros x y.
unfold Fcomp2.
generalize (Fshift2_correct x y).
destruct (Fshift2 x y) as ((mx, my), e).
intros (Hx, Hy).
rewrite <- Hx, <- Hy.
unfold float2R, F2R. simpl.
rewrite Rcompare_mult_r.
now rewrite Rcompare_Z2R.
apply bpow_gt_0.
Qed.

Lemma power_radix_pos :
  forall r e, (0 < powerRZ (P2R r) e)%R.
intros.
apply powerRZ_lt.
change (P2R r) with (Z2R (Zpos r)).
apply (Z2R_lt 0).
exact (refl_equal _).
Qed.

Definition Feq2 (x y : float2) :=
 match Fcomp2 x y with
 | Eq => true
 | _ => false
 end.

Lemma Feq2_correct :
  forall x y : float2,
  Feq2 x y = true -> x = y :>R.
Proof.
intros x y Hb.
apply Rcompare_Eq_inv.
rewrite <- Fcomp2_correct.
revert Hb.
unfold Feq2.
now case Fcomp2.
Qed.

Definition Flt2 (x y : float2) :=
 match Fcomp2 x y with
 | Lt => true
 | _ => false
 end.

Lemma Flt2_correct :
  forall x y : float2,
  Flt2 x y = true -> (x < y)%R.
Proof.
intros x y Hb.
apply Rcompare_Lt_inv.
rewrite <- Fcomp2_correct.
revert Hb.
unfold Flt2.
now case Fcomp2.
Qed.

Definition Fle2 (x y : float2) :=
 match Fcomp2 x y with
 | Gt => false
 | _ => true
 end.

Lemma Fle2_correct :
  forall x y : float2,
  Fle2 x y = true -> (x <= y)%R.
Proof.
intros x y Hb.
apply Rcompare_not_Gt_inv.
rewrite <- Fcomp2_correct.
intros H.
unfold Fle2 in Hb.
now rewrite H in Hb.
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
apply Rcompare_Gt_inv.
now rewrite <- Fcomp2_correct.
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
Proof.
intros (m, e) H.
unfold float2R.
apply F2R_gt_0_compat. simpl.
revert H.
unfold Fpos. simpl.
now case m.
Qed.

Definition Fneg (x : float2) :=
 match (Fnum x) with
   Zneg _ => true
 | _ => false
 end.

Lemma Fneg_correct :
  forall x : float2,
  Fneg x = true -> (x < 0)%R.
Proof.
intros (m, e) H.
unfold float2R.
apply F2R_lt_0_compat. simpl.
revert H.
unfold Fpos. simpl.
now case m.
Qed.

Definition Fpos0 (x : float2) :=
 match (Fnum x) with
   Zneg _ => false
 | _ => true
 end.

Lemma Fpos0_correct :
  forall x : float2,
  Fpos0 x = true -> (0 <= x)%R.
Proof.
intros (m, e) H.
unfold float2R.
apply F2R_ge_0_compat. simpl.
revert H.
unfold Fpos. simpl.
now case m.
Qed.

Definition Fneg0 (x : float2) :=
 match (Fnum x) with
   Zpos _ => false
 | _ => true
 end.

Lemma Fneg0_correct :
  forall x : float2,
  Fneg0 x = true -> (x <= 0)%R.
Proof.
intros (m, e) H.
unfold float2R.
apply F2R_le_0_compat. simpl.
revert H.
unfold Fpos. simpl.
now case m.
Qed.

Definition Flt2_m1 f :=
  Flt2 (Float2 (-1) 0) f.

Lemma Flt2_m1_correct :
  forall f,
  Flt2_m1 f = true ->
  (-1 < f)%R.
Proof.
intros f Hb.
generalize (Flt2_correct _ _ Hb).
unfold float2R, F2R. simpl.
now rewrite Rmult_1_r.
Qed.

End Gappa_dyadic.
