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

End Gappa_round_aux.
