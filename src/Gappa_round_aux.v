Require Import ZArith.
Require Import Reals.
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Fcalc_digits.
Require Import Fcore_float_prop.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.

Section Gappa_round_aux.

Lemma float2_shift_p1 :
  forall e m : Z,
  Float2 m (e + 1) = Float2 (m * 2) e :>R.
Proof.
intros e m.
unfold float2R, F2R. simpl.
rewrite bpow_add.
rewrite mult_Z2R.
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
  Zpos (digits m) = Fcalc_digits.digits radix2 (Zpos m).
Proof.
intros m.
apply trans_eq with (Z_of_nat (S (Fcalc_digits.digits2_Pnat m))).
(* *)
induction m ; simpl.
now rewrite 2!Zpos_succ_morphism, IHm.
now rewrite 2!Zpos_succ_morphism, IHm.
easy.
(* *)
rewrite Fcalc_digits.digits_ln_beta. 2: easy.
apply sym_eq.
apply ln_beta_unique.
generalize (Fcalc_digits.digits2_Pnat_correct m).
generalize (Fcalc_digits.digits2_Pnat m).
intros d H.
simpl in H.
replace (Z_of_nat (S d) - 1)%Z with (Z_of_nat d).
rewrite <- abs_Z2R.
rewrite <- 2!Z2R_Zpower_nat.
split.
now apply Z2R_le.
now apply Z2R_lt.
rewrite inj_S.
apply Zpred_succ.
Qed.

Lemma float2_digits_correct :
  forall m e,
  (Float2 1 (e + Zpos (digits m) - 1)%Z <= Float2 (Zpos m) e < Float2 1 (e + Zpos (digits m))%Z)%R.
Proof.
intros m e.
rewrite digits2_digits.
rewrite Fcalc_digits.digits_ln_beta. 2: easy.
unfold float2R, Fnum, Fexp.
rewrite 2!F2R_bpow.
unfold Zminus.
rewrite bpow_add.
rewrite Zplus_comm.
rewrite <- ln_beta_F2R. 2: easy.
rewrite <- bpow_add.
destruct (ln_beta radix2 (F2R (Fcore_defs.Float radix2 (Zpos m) e))) as (e', He).
simpl. change (Zpos m) with (Zabs (Zpos m)).
rewrite <- abs_F2R.
apply He.
intros H.
discriminate (F2R_eq_0_reg _ _ _ H).
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

End Gappa_round_aux.
