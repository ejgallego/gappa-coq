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

Lemma float2_pow2_le :
 forall k l : Z, (Float2 1 k <= Float2 1 l)%R ->
 (k <= l)%Z.
intros k l H.
apply Znot_gt_le.
intro H0.
elim Rle_not_lt with (1 := H).
apply float2_Rlt_pow2.
apply Zgt_lt.
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

Lemma Zpos_pos_of_Z_minus :
 forall a b : Z, (a < b)%Z ->
 (Zpos (pos_of_Z (b - a)) = b - a)%Z.
intros a b H.
assert (0 < b - a)%Z. omega.
destruct (b - a)%Z ; compute in H0 ; try discriminate H0.
apply refl_equal.
Qed.

Lemma Zneg_pos_of_Z_minus :
 forall a b : Z, (a < b)%Z ->
 (Zneg (pos_of_Z (b - a)) = a - b)%Z.
intros a b H.
assert (0 < b - a)%Z. omega.
cutrewrite (a - b = -(b - a))%Z. 2: ring.
destruct (b - a)%Z ; compute in H0 ; try discriminate H0.
apply refl_equal.
Qed.

Lemma float2_repartition :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 (e2 < e1)%Z /\ (e1 + Zpos (digits m1) = e2 + Zpos (digits m2))%Z.
intros m1 m2 e1 e2 H.
split.
apply Znot_ge_lt.
intros H0.
generalize (Zle_lt_or_eq _ _ (Zge_le _ _ H0)).
(* e1 < e2 *)
clear H0. intros [H0|H0].
generalize (Fshift2_correct (Float2 (Zpos m1) e1) (Float2 (Zpos m2) e2)).
unfold Fshift2.
simpl.
rewrite <- (Zneg_pos_of_Z_minus _ _ H0).
intros (_,H1).
generalize H.
rewrite <- H1.
clear H H0 H1.
unfold float2R. simpl.
do 3 rewrite F2R_split.
do 3 rewrite <- (Rmult_comm (powerRZ (P2R 2) e1)).
intros (H1,H2).
assert (0 < powerRZ (P2R 2) e1)%R by apply power_radix_pos.
generalize (Rmult_lt_reg_l _ _ _ H H1). clear H1. intro H1.
generalize (lt_Z2R _ _ H1). clear H1. intro H1.
generalize (Rmult_lt_reg_l _ _ _ H H2). clear H2. intro H2.
generalize (lt_Z2R _ _ H2). clear H2. intro H2.
change (Zpos (m1 + 1)) with (Zpos m1 + 1)%Z in H2.
omega.
(* e1 = e2 *)
generalize H. clear H.
rewrite H0.
unfold float2R.
do 3 rewrite F2R_split.
do 3 rewrite <- (Rmult_comm (powerRZ (P2R 2) e2)).
clear H0. intros (H1, H2).
assert (0 < powerRZ (P2R 2) e2)%R by apply power_radix_pos.
generalize (Rmult_lt_reg_l _ _ _ H H1). clear H1. intro H1.
generalize (lt_Z2R _ _ H1). clear H1. intro H1.
generalize (Rmult_lt_reg_l _ _ _ H H2). clear H2. intro H2.
generalize (lt_Z2R _ _ H2). clear H2. intro H2.
simpl in H1, H2.
change (Zpos (m1 + 1)) with (Zpos m1 + 1)%Z in H2.
omega.
(* . *)
generalize (float2_digits_correct m1 e1).
generalize (float2_digits_correct m2 e2).
intros (H0,H1) (H2,H3).
generalize (Rlt_trans _ _ _ (Rle_lt_trans _ _ _ H2 (proj1 H)) H1).
cut (Float2 (Zpos m1 + 1) e1 <= Float2 1 (e1 + Zpos (digits m1)))%R.
intro H4.
generalize (Rle_lt_trans _ _ _ H0 (Rlt_le_trans _ _ _ (proj2 H) H4)).
clear H H0 H1 H2 H3 H4.
intros H1 H2.
generalize (float2_pow2_lt _ _ H1).
generalize (float2_pow2_lt _ _ H2).
omega.
clear H H0 H1 H2 H3 m2 e2.
rewrite <- (float2_shl_correct 1 (e1 + Zpos (digits m1)) (digits m1)).
simpl.
cutrewrite (e1 + Zpos (digits m1) - Zpos (digits m1) = e1)%Z. 2: ring.
apply float2_binade_le.
rewrite shift_pos_nat.
unfold shift_nat.
induction m1.
simpl.
rewrite nat_of_P_succ_morphism.
simpl.
rewrite Pplus_one_succ_r.
exact IHm1.
simpl.
rewrite nat_of_P_succ_morphism.
simpl.
change (Zpos (xI m1)) with (2 * Zpos m1 + 1)%Z.
change (Zpos (xO (iter_nat (nat_of_P (digits m1)) positive xO xH))) with
  (2 * Zpos (iter_nat (nat_of_P (digits m1)) positive xO xH))%Z.
change (Zpos (m1 + 1)) with (Zpos m1 + 1)%Z in IHm1.
omega.
apply Zle_refl.
Qed.

End Gappa_round_aux.
