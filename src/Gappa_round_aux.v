Require Import ZArith.
Require Import Reals.
Require Import Flocq.Core.Fcore_Raux.
Require Import Flocq.Core.Fcore_defs.
Require Import Flocq.Core.Fcore_digits.
Require Import Flocq.Calc.Fcalc_digits.
Require Import Flocq.Core.Fcore_float_prop.
Require Import Flocq.Core.Fcore_generic_fmt.
Require Import Flocq.Core.Fcore_FIX.
Require Import Flocq.Core.Fcore_FLX.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.

Section Gappa_round_aux.

Lemma float2_shift_p1 :
  forall e m : Z,
  Float2 m (e + 1) = Float2 (m * 2) e :>R.
Proof.
intros e m.
unfold float2R, F2R. simpl.
rewrite bpow_plus.
rewrite Z2R_mult.
simpl.
ring.
Qed.

Fixpoint digits (m : positive) : positive :=
 match m with
 | xH => xH
 | xI p => Psucc (digits p)
 | xO p => Psucc (digits p)
 end.

Lemma digits2_digits :
  forall m : positive,
  Zpos (digits m) = Zdigits radix2 (Zpos m).
Proof.
intros m.
apply trans_eq with (Z_of_nat (S (digits2_Pnat m))).
(* *)
induction m ; simpl.
now rewrite 2!Zpos_succ_morphism, IHm.
now rewrite 2!Zpos_succ_morphism, IHm.
easy.
(* *)
rewrite Zdigits_ln_beta. 2: easy.
apply sym_eq.
apply ln_beta_unique.
generalize (digits2_Pnat_correct m).
generalize (digits2_Pnat m).
intros d H.
simpl in H.
replace (Z_of_nat (S d) - 1)%Z with (Z_of_nat d).
rewrite <- Z2R_abs.
rewrite <- 2!Z2R_Zpower_nat.
split.
now apply Z2R_le.
now apply Z2R_lt.
rewrite inj_S.
apply Zpred_succ.
Qed.

Definition pos_of_Z (n : Z) :=
 match n with
 | Zpos p => p
 | _ => xH
 end.

Lemma Zpos_pos_of_Z :
 forall a : Z, (0 < a)%Z ->
 (Zpos (pos_of_Z a) = a)%Z.
induction a ; intros ; compute in H ; try discriminate H.
exact (refl_equal _).
Qed.

Lemma FIX_iff_generic :
  forall k x,
  FIX x k <-> generic_format radix2 (FIX_exp k) x.
Proof.
intros k x.
split.
intros ((m,e),(H1,H2)).
rewrite <- H1.
now apply generic_format_F2R.
intros H.
destruct (FIX_format_generic _ _ _ H) as ((m,e),(H1,H2)).
exists (Float2 m e) ; repeat split.
easy.
rewrite <- H2.
apply Zle_refl.
Qed.

Lemma FLT_iff_generic :
  forall p x,
  FLT x p <-> generic_format radix2 (FLX_exp (Zpos p)) x.
Proof.
intros p x.
split.
intros ((m,e),(H1,H2)).
apply generic_format_FLX.
exists (Float radix2 m e).
now split.
intros H.
destruct (@FLX_format_generic _ (Zpos p) (refl_equal Lt) _ H) as ((m,e),(H1,H2)).
now exists (Float2 m e) ; repeat split.
Qed.

Lemma fix_le :
  forall x : R, forall xn zn : Z,
  FIX x xn ->
  (zn <= xn)%Z ->
  FIX x zn.
Proof.
intros x xn zn (xf,(Hx1,Hx2)) H.
exists xf.
split.
exact Hx1.
apply Zle_trans with (1 := H) (2 := Hx2).
Qed.

Lemma flt_le :
  forall x : R, forall xn zn : positive,
  FLT x xn ->
  (Zpos xn <= Zpos zn)%Z ->
  FLT x zn.
Proof.
intros x xn zn (xf,(Hx1,Hx2)) H.
exists xf.
split.
exact Hx1.
apply Zlt_le_trans with (1 := Hx2).
apply le_Z2R.
change (Z2R (Zpower radix2 (Zpos xn)) <= Z2R (Zpower radix2 (Zpos zn)))%R.
apply Z2R_le.
now apply Zpower_le.
Qed.

End Gappa_round_aux.
