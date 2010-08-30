Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_integer.

Require Fcore_defs.
Require Fcalc_digits.
Require Import Fcore_float_prop.

Section Gappa_round_aux.

Definition radix2 := Build_radix 2 (refl_equal true).

Lemma float2_float :
  forall m e,
  float2R (Float2 m e) = Fcore_defs.F2R (Fcore_defs.Float radix2 m e).
Proof.
intros m e.
unfold float2R, Fcore_defs.F2R. simpl.
rewrite F2R_split.
apply f_equal.
apply sym_eq.
apply bpow_powerRZ.
Qed.

Lemma float2_shift_p1 :
 forall e : Z, forall m : Z,
 Float2 m (e + 1) = Float2 (m * 2) e :>R.
intros e m.
unfold float2R. simpl.
do 2 rewrite F2R_split.
rewrite powerRZ_add.
rewrite mult_Z2R.
simpl.
ring.
apply Rgt_not_eq.
exact (Z2R_lt 0 2 (refl_equal _)).
Qed.

Lemma float2_shift_m1 :
 forall e : Z, forall m : Z,
 Float2 m e = Float2 (m * 2) (e - 1) :>R.
intros e m.
pattern e at 1 ; replace e with (e - 1 + 1)%Z. 2: ring.
apply float2_shift_p1.
Qed.

Lemma float2_binade_lt :
  forall m1 m2 e,
  (m1 < m2)%Z -> (Float2 m1 e < Float2 m2 e)%R.
Proof.
intros m1 m2 e H.
do 2 rewrite float2_float.
now apply F2R_lt_compat.
Qed.

Lemma float2_binade_le :
  forall m1 m2 e,
  (m1 <= m2)%Z -> (Float2 m1 e <= Float2 m2 e)%R.
Proof.
intros m1 m2 e H.
do 2 rewrite float2_float.
now apply F2R_le_compat.
Qed.

Lemma float2_binade_eq_reg :
  forall m1 m2 e,
  Float2 m1 e = Float2 m2 e :>R ->
  m1 = m2.
Proof.
intros m1 m2 e H.
apply F2R_eq_reg with radix2 e.
now do 2 rewrite <- float2_float.
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

Lemma digits_correct :
  forall m : positive,
  (powerRZ 2 (Zpos (digits m) - 1)%Z <= Z2R (Zpos m) < powerRZ 2 (Zpos (digits m)))%R.
Proof.
intros m.
rewrite digits2_digits.
rewrite <- 2!(bpow_powerRZ radix2).
rewrite Fcalc_digits.digits_ln_beta. 2: easy.
destruct (ln_beta radix2 (Z2R (Zpos m))) as (e, H).
simpl.
rewrite <- abs_Z2R in H.
apply H.
now apply (Z2R_neq _ 0).
Qed.

Lemma digits_pow2 :
 forall m p : positive,
 (Zpos m < Zpower_pos 2 p)%Z ->
 (Zpos (digits m) <= Zpos p)%Z.
induction m ; intros.
destruct (Psucc_pred p) as [H0|H0].
elim Zle_not_lt with (2 := H).
rewrite H0.
unfold Zpower_pos. simpl.
rewrite Zpos_xI.
generalize (Zgt_pos_0 m).
omega.
rewrite <- H0.
simpl.
repeat rewrite Zpos_succ_morphism.
unfold Zsucc.
apply Zplus_le_compat_r.
apply IHm.
cut (2 * Zpos m + 1 < 2 * Zpower_pos 2 (Ppred p))%Z.
omega.
cutrewrite (2 * Zpower_pos 2 (Ppred p) = Zpower_pos 2 p)%Z.
exact H.
pattern p at 2 ; rewrite <- H0.
repeat rewrite Zpower_pos_nat.
rewrite nat_of_P_succ_morphism.
exact (refl_equal _).
destruct (Psucc_pred p) as [H0|H0].
elim Zle_not_lt with (2 := H).
rewrite H0.
unfold Zpower_pos. simpl.
rewrite (Zpos_xO m).
generalize (Zgt_pos_0 m).
omega.
rewrite <- H0.
simpl.
repeat rewrite Zpos_succ_morphism.
unfold Zsucc.
apply Zplus_le_compat_r.
apply IHm.
cut (2 * Zpos m < 2 * Zpower_pos 2 (Ppred p))%Z.
omega.
cutrewrite (2 * Zpower_pos 2 (Ppred p) = Zpower_pos 2 p)%Z.
exact H.
pattern p at 2 ; rewrite <- H0.
repeat rewrite Zpower_pos_nat.
rewrite nat_of_P_succ_morphism.
exact (refl_equal _).
simpl.
generalize (Zgt_pos_0 p).
omega.
Qed.

Lemma digits_succ :
 forall m : positive,
 digits (Psucc m) = digits m \/
 (digits (Psucc m) = Psucc (digits m) /\ Psucc m = iter_pos (digits m) _ xO xH).
intros m.
rewrite iter_nat_of_P.
induction m.
simpl.
destruct IHm.
left.
rewrite H.
exact (refl_equal _).
right.
split.
rewrite (proj1 H).
exact (refl_equal _).
rewrite (proj2 H).
rewrite nat_of_P_succ_morphism.
exact (refl_equal _).
left.
exact (refl_equal _).
right.
split ; exact (refl_equal _).
Qed.

Lemma float2_pow2 :
  forall e,
  Float2 1 e = powerRZ 2 e :>R.
intros.
unfold float2R.
rewrite F2R_split.
rewrite Rmult_1_l.
apply refl_equal.
Qed.

Lemma float2_digits_correct :
 forall m : positive, forall e: Z,
 (Float2 1 (e + Zpos (digits m) - 1)%Z <= Float2 (Zpos m) e < Float2 1 (e + Zpos (digits m))%Z)%R.
intros m e.
generalize (digits_correct m). intros (H1,H2).
do 2 rewrite float2_pow2.
unfold float2R.
rewrite F2R_split.
simpl.
split.
unfold Zminus.
rewrite <- Zplus_assoc.
rewrite powerRZ_add.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
auto with real.
exact H1.
discrR.
rewrite powerRZ_add.
rewrite Rmult_comm.
apply Rmult_lt_compat_l.
auto with real.
exact H2.
discrR.
Qed.

Lemma float2_Rlt_pow2 :
 forall k l : Z, (k < l)%Z ->
 (Float2 1 k < Float2 1 l)%R.
intros k l H.
do 2 rewrite float2_pow2.
replace l with (l - k + k)%Z by ring.
rewrite powerRZ_add. 2: discrR.
pattern (powerRZ 2 k) at 1 ; (rewrite <- Rmult_1_l).
apply Rmult_lt_compat_r.
auto with real.
unfold powerRZ.
assert (0 < l - k)%Z by omega.
clear H.
induction (l - k)%Z.
discriminate H0.
apply Rlt_pow_R1.
auto with real.
apply lt_O_nat_of_P.
discriminate H0.
Qed.

Lemma float2_Rle_pow2 :
 forall k l : Z, (k <= l)%Z ->
 (Float2 1 k <= Float2 1 l)%R.
intros k l H.
destruct (Zle_lt_or_eq _ _ H).
apply Rlt_le.
apply float2_Rlt_pow2.
exact H0.
rewrite H0.
apply Rle_refl.
Qed.

Lemma float2_pow2_lt :
 forall k l : Z, (Float2 1 k < Float2 1 l)%R ->
 (k < l)%Z.
intros k l H.
apply Znot_ge_lt.
intro H0.
elim Rlt_not_le with (1 := H).
apply float2_Rle_pow2.
apply Zge_le.
exact H0.
Qed.

Lemma float2_pos_reg :
 forall m e : Z,
 (0 < Float2 m e)%R ->
 (0 < m)%Z.
intros m e H.
apply lt_Z2R.
apply Rmult_lt_reg_l with (powerRZ (P2R 2) e).
apply power_radix_pos.
rewrite Rmult_0_r.
rewrite Rmult_comm.
rewrite <- F2R_split.
exact H.
Qed.

Lemma float2_pos_compat :
 forall m e : Z,
 (0 < m)%Z ->
 (0 < Float2 m e)%R.
intros m e H.
rewrite <- (float2_zero e).
exact (float2_binade_lt _ _ _ H).
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
