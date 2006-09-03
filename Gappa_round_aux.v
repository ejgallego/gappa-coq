Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.

Section Gappa_round_aux.

Lemma float2_shift_p1 :
 forall e : Z, forall m : Z,
 Float2 m (e + 1) = Float2 (m * 2) e :>R.
intros e m.
unfold float2R. simpl.
rewrite powerRZ_add. 2: discrR.
rewrite mult_IZR.
simpl.
replace (IZR 2) with 2%R. 2: apply refl_equal.
ring.
Qed.

Lemma float2_shift_m1 :
 forall e : Z, forall m : Z,
 Float2 m e = Float2 (m * 2) (e - 1) :>R.
intros e m.
pattern e at 1 ; replace e with (e - 1 + 1)%Z. 2: ring.
apply float2_shift_p1.
Qed.

Lemma float2_binade_lt :
 forall m1 m2 : Z, forall e : Z,
 (m1 < m2)%Z -> (Float2 m1 e < Float2 m2 e)%R.
intros m1 m2 e H.
unfold float2R. simpl.
apply Rmult_lt_compat_r.
auto with real.
apply IZR_lt with (1 := H).
Qed.

Lemma float2_binade_le :
 forall m1 m2 : Z, forall e : Z,
 (m1 <= m2)%Z -> (Float2 m1 e <= Float2 m2 e)%R.
intros m1 m2 e H.
unfold float2R. simpl.
apply Rmult_le_compat_r.
auto with real.
apply IZR_le with (1 := H).
Qed.

Lemma float2_binade_eq_reg :
 forall m1 m2 : Z, forall e : Z,
 Float2 m1 e = Float2 m2 e :>R ->
 m1 = m2.
intros.
destruct (Ztrichotomy m1 m2) as [H0|[H0|H0]].
2: exact H0.
elim Rlt_not_eq with (2 := H).
exact (float2_binade_lt _ _ _ H0).
elim Rgt_not_eq with (2 := H).
exact (float2_binade_lt _ _ _ (Zgt_lt _ _ H0)).
Qed.


Fixpoint digits (m : positive) : positive :=
 match m with
 | xH => xH
 | xI p => Psucc (digits p)
 | xO p => Psucc (digits p)
 end.

Lemma digits_correct :
 forall m : positive,
 (powerRZ 2 (Zpos (digits m) - 1)%Z <= IZR (Zpos m) < powerRZ 2 (Zpos (digits m)))%R.
intros m.
induction m.
simpl (digits (xI m)).
rewrite Zpos_succ_morphism.
unfold Zsucc, Zminus.
rewrite <- Zplus_assoc. rewrite (Zplus_comm 1). rewrite Zplus_assoc.
rewrite Zpos_xI.
split ; (rewrite powerRZ_add ; [
  rewrite Rmult_comm ;
  simpl (powerRZ 2 1) ;
  rewrite Rmult_1_r | discrR ]).
apply Rle_trans with (IZR 2 * IZR (Zpos m))%R.
apply Rmult_le_compat_l.
simpl. auto with real.
exact (proj1 IHm).
rewrite <- mult_IZR.
apply IZR_le.
exact (Zle_succ _).
apply Rlt_le_trans with (IZR 2 * (IZR (Zpos m) + IZR 1))%R.
rewrite <- plus_IZR.
rewrite <- mult_IZR.
apply IZR_lt.
omega.
apply Rmult_le_compat_l.
auto with real.
rewrite <- plus_IZR.
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P (digits m)).
cutrewrite (2 = INR 2)%R. 2: apply refl_equal.
rewrite <- Zpower_nat_powerRZ.
apply IZR_le.
apply (Zlt_le_succ (Zpos m)).
apply lt_IZR.
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
exact (proj2 IHm).
simpl (digits (xO m)).
rewrite Zpos_succ_morphism.
unfold Zsucc, Zminus.
rewrite <- Zplus_assoc. rewrite (Zplus_comm 1). rewrite Zplus_assoc.
rewrite Zpos_xO.
split ; (rewrite powerRZ_add ; [
  rewrite Rmult_comm ;
  simpl (powerRZ 2 1) ;
  rewrite Rmult_1_r | discrR ]).
rewrite mult_IZR.
apply Rmult_le_compat_l.
simpl. auto with real.
exact (proj1 IHm).
rewrite mult_IZR.
apply Rmult_lt_compat_l.
auto with real.
exact (proj2 IHm).
simpl.
rewrite Rmult_1_r.
auto with real.
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

Lemma float2_digits_correct :
 forall m : positive, forall e: Z,
 (Float2 1 (e + Zpos (digits m) - 1)%Z <= Float2 (Zpos m) e < Float2 1 (e + Zpos (digits m))%Z)%R.
intros m e.
generalize (digits_correct m). intros (H1,H2).
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
split.
unfold Zminus.
rewrite <- Zplus_assoc.
rewrite powerRZ_add. 2: discrR.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
auto with real.
exact H1.
rewrite powerRZ_add. 2: discrR.
rewrite Rmult_comm.
apply Rmult_lt_compat_l.
auto with real.
exact H2.
Qed.

Definition pos_of_Z (n : Z) :=
 match n with
 | Zpos p => p
 | _ => xH
 end.

Lemma float2_Rle_pow2 :
 forall k l : Z, (k <= l)%Z ->
 (Float2 1 k <= Float2 1 l)%R.
intros k l H.
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
cutrewrite (l = l - k + k)%Z. 2: ring.
rewrite powerRZ_add. 2: discrR.
pattern (powerRZ 2 k) at 1 ; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
auto with real.
unfold powerRZ.
cut (0 <= l - k)%Z. 2: omega.
clear H.
case (l - k)%Z ; intros.
apply Rle_refl.
apply pow_R1_Rle.
auto with real.
elim Zle_not_lt with (1 := H).
exact (Zlt_neg_0 p).
Qed.

Lemma float2_pow2_lt :
 forall k l : Z, (Float2 1 k < Float2 1 l)%R ->
 (k < l)%Z.
intros k l.
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
intros H.
cutrewrite (l = k + (l - k))%Z in H. 2: ring.
rewrite powerRZ_add in H. 2: discrR.
pattern (powerRZ 2 k) at 1 in H ; rewrite <- Rmult_1_r in H.
assert (0 < l - k)%Z. 2: omega.
assert (0 < powerRZ 2 k)%R. auto with real.
generalize (Rmult_lt_reg_l _ _ _ H0 H).
unfold powerRZ.
case (l - k)%Z ; intros.
elim (Rlt_irrefl _ H1).
exact (Zgt_lt _ _ (Zgt_pos_0 p)).
elim Rlt_not_le with (1 := H1).
apply Rmult_le_reg_l with (2 ^ nat_of_P p)%R.
auto with real.
rewrite Rinv_r.
rewrite Rmult_1_r.
auto with real.
apply Rgt_not_eq.
unfold Rgt.
auto with real.
Qed.

Lemma float2_Rlt_pow2 :
 forall k l : Z, (k < l)%Z ->
 (Float2 1 k < Float2 1 l)%R.
intros k l H.
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
cutrewrite (l = l - k + k)%Z. 2: ring.
rewrite powerRZ_add. 2: discrR.
pattern (powerRZ 2 k) at 1 ; rewrite <- Rmult_1_l.
apply Rmult_lt_compat_r.
auto with real.
unfold powerRZ.
cut (0 < l - k)%Z. 2: omega.
clear H.
case (l - k)%Z ; intros.
elim (Zlt_irrefl _ H).
apply Rlt_pow_R1.
auto with real.
apply lt_O_nat_of_P.
elim Zlt_not_le with (1 := H).
apply Zlt_le_weak.
exact (Zlt_neg_0 p).
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
repeat rewrite <- (Rmult_comm (powerRZ 2 e1)).
intros (H1,H2).
assert (0 < powerRZ 2 e1)%R. auto with real.
generalize (Rmult_lt_reg_l _ _ _ H H1). clear H1. intro H1.
generalize (INR_lt _ _ H1). clear H1. intro H1.
generalize (Rmult_lt_reg_l _ _ _ H H2). clear H2. intro H2.
generalize (INR_lt _ _ H2). clear H2. intro H2.
apply lt_not_le with (1 := H2).
rewrite nat_of_P_plus_morphism.
replace (nat_of_P 1) with 1. 2: apply refl_equal.
omega.
generalize H.
unfold float2R. simpl.
rewrite <- H0.
clear H H0.
repeat rewrite <- (Rmult_comm (powerRZ 2 e1)).
intros (H1,H2).
assert (0 < powerRZ 2 e1)%R. auto with real.
generalize (Rmult_lt_reg_l _ _ _ H H1). clear H1. intro H1.
generalize (INR_lt _ _ H1). clear H1. intro H1.
generalize (Rmult_lt_reg_l _ _ _ H H2). clear H2. intro H2.
generalize (INR_lt _ _ H2). clear H2. intro H2.
apply lt_not_le with (1 := H2).
rewrite nat_of_P_plus_morphism.
replace (nat_of_P 1) with 1. 2: apply refl_equal.
omega.
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
rewrite <- (float2_shl_correct (Float2 1 (e1 + Zpos (digits m1))) (digits m1)).
simpl.
ring (e1 + Zpos (digits m1) - Zpos (digits m1))%Z.
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
cutrewrite (Zpos (xI m1) = 2 * Zpos m1 + 1)%Z. 2: apply refl_equal.
cutrewrite (Zpos (xO (iter_nat (nat_of_P (digits m1)) positive xO xH)) =
  2 * Zpos (iter_nat (nat_of_P (digits m1)) positive xO xH))%Z.
2: apply refl_equal.
cutrewrite (Zpos (m1 + 1) = Zpos m1 + 1)%Z in IHm1. 2: apply refl_equal.
omega.
apply Zle_refl.
Qed.

Lemma float2_repartition_underflow :
 forall m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m2) e2 < Float2 1 e1)%R ->
 (e2 + Zpos (digits m2) <= e1)%Z.
intros m2 e1 e2 Hf.
generalize (proj1 (float2_digits_correct m2 e2)).
intros H1.
apply Znot_gt_le.
intro H.
apply (Rlt_not_le _ _ (Rle_lt_trans _ _ _ H1 Hf)).
apply float2_Rle_pow2.
omega.
Qed.

End Gappa_round_aux.
