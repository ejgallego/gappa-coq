Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_pred_bnd.
Require Import Gappa_round_def.
Require Import Gappa_round.

Section Gappa_float.

Definition float_shift (p : positive) (d b : Z) :=
 Zmax (b - Zpos p) (-d).

Lemma good_shift :
 forall p : positive, forall m : Z,
 good_rexp (float_shift p m).
unfold float_shift. split.
assert (k - Zpos p < k -> -m < k -> k + 1 - Zpos p <= k /\ -m <= k)%Z.
omega.
intro H0.
generalize (Zle_lt_trans _ _ _ (Zmax1 (k - Zpos p) (-m)) H0).
generalize (Zle_lt_trans _ _ _ (Zmax2 (k - Zpos p) (-m)) H0).
intros H1 H2.
generalize (H H2 H1).
clear H H0 H1 H2. intros (H1,H2).
unfold Zmax.
case (k + 1 - Zpos p ?= - m)%Z ; assumption.
intro H.
generalize (Zgt_pos_0 p). intro H0.
cutrewrite (Zmax (k - Zpos p) (-m) = (-m))%Z.
clear H. unfold Zmax.
split.
case (-m + 1 - Zpos p ?= -m)%Z ; omega.
intros.
assert (l - Zpos p < -m)%Z. omega.
rewrite H1.
apply refl_equal.
generalize H. clear H.
unfold Zmax.
case (k - Zpos p ?= - m)%Z ; intros ; omega.
Qed.

Definition rounding_float (rdir : round_dir) (p : positive) (d : Z) :=
 round_extension rdir (float_shift p d) (good_shift p d).

Theorem fix_of_float :
 forall rdir : round_dir,
 forall x : R, forall p : positive, forall k1 k2 : Z,
 Zle_bool k2 (-k1) = true ->
 FIX (rounding_float rdir p k1 x) k2.
intros rdir x p k1 k2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX, rounding_float.
destruct (representable_round_extension rdir _ (good_shift p k1) x) as (m,(e,(H1,H2))).
induction m.
exists (Float2 0 k2).
split.
rewrite H1.
unfold float2R.
repeat rewrite Rmult_0_l.
exact (refl_equal _).
exact (Zle_refl _).
exists (Float2 (Zpos p0) e).
split.
exact (sym_eq H1).
apply Zle_trans with (1 := H).
unfold rexp_representable, float_shift in H2.
apply Zle_trans with (2 := H2).
exact (Zle_max_r _ _).
exists (Float2 (Zneg p0) e).
split.
exact (sym_eq H1).
apply Zle_trans with (1 := H).
unfold rexp_representable, float_shift in H2.
apply Zle_trans with (2 := H2).
exact (Zle_max_r _ _).
Qed.

Theorem flt_of_float :
 forall rdir : round_dir,
 forall x : R, forall p1 p2 : positive, forall k : Z,
 Zle_bool (Zpos p1) (Zpos p2) = true ->
 FLT (rounding_float rdir p1 k x) p2.
intros rdir x p1 p2 k H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FLT, rounding_float.
destruct (representable_round_extension rdir _ (good_shift p1 k) x) as (m,(e,(H1,H2))).
exists (Float2 m e).
split.
exact (sym_eq H1).
unfold rexp_representable, float_shift in H2.
clear H1.
induction m.
apply Gappa_decimal.Zpower_pos_pos.
simpl.
apply lt_IZR.
rewrite Zpower_pos_nat.
replace 2%Z with (Z_of_nat 2). 2: apply refl_equal.
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
apply Rlt_le_trans with (1 := proj2 (digits_correct p)).
assert (Float2 1 (Zpos (digits p)) <= Float2 1 (Zpos p2))%R.
apply Rle_trans with (2 := float2_Rle_pow2 _ _ H).
apply float2_Rle_pow2.
generalize (Zle_max_l (e + Zpos (digits p) - Zpos p1) (- k)).
omega.
unfold float2R in H0.
repeat rewrite Rmult_1_l in H0.
exact H0.
simpl.
apply lt_IZR.
rewrite Zpower_pos_nat.
replace 2%Z with (Z_of_nat 2). 2: apply refl_equal.
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
apply Rlt_le_trans with (1 := proj2 (digits_correct p)).
assert (Float2 1 (Zpos (digits p)) <= Float2 1 (Zpos p2))%R.
apply Rle_trans with (2 := float2_Rle_pow2 _ _ H).
apply float2_Rle_pow2.
generalize (Zle_max_l (e + Zpos (digits p) - Zpos p1) (- k)).
omega.
unfold float2R in H0.
repeat rewrite Rmult_1_l in H0.
exact H0.
Qed.

Theorem float_of_fix_flt :
 forall rdir : round_dir,
 forall x : R, forall xi : FF,
 forall d1 d2 : Z, forall p1 p2 : positive,
 FIX x d1 -> FLT x p1 ->
 Zle_bool (-d2) d1 && Zle_bool (Zpos p1) (Zpos p2) && contains_zero_helper xi = true ->
 BND (rounding_float rdir p2 d2 x - x) xi.
intros rdir x xi d1 d2 p1 p2 (f1,(Hx1,Hx2)) (f2,(Hx3,Hx4)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
cutrewrite (rounding_float rdir p2 d2 x = x :>R).
unfold Rminus.
rewrite (Rplus_opp_r x).
apply contains_zero with (1 := H3).
cut (exists f : float2, x = f /\ (d1 <= Fexp f)%Z /\ (Zabs (Fnum f) < Zpower_pos 2 p1)%Z).
intros (f,(Hx5,(Hx6,Hx7))).
rewrite Hx5.
unfold rounding_float.
rewrite round_extension_float2.
induction f.
induction Fnum.
unfold round, float2R. simpl.
repeat rewrite Rmult_0_l.
apply refl_equal.
unfold round. simpl.
rewrite round_rexp_exact.
apply refl_equal.
unfold float_shift, Zmax.
simpl in Hx6, Hx7.
cut (Zpos (digits p) <= Zpos p2)%Z. intro H.
case (Fexp + Zpos (digits p) - Zpos p2 ?= - d2)%Z.
omega.
exact (Zle_trans _ _ _ H1 Hx6).
omega.
apply Zle_trans with (2 := H2).
exact (digits_pow2 _ _ Hx7).
unfold round. simpl.
rewrite round_rexp_exact.
apply refl_equal.
unfold float_shift, Zmax.
simpl in Hx6, Hx7.
cut (Zpos (digits p) <= Zpos p2)%Z. intro H.
case (Fexp + Zpos (digits p) - Zpos p2 ?= - d2)%Z.
omega.
exact (Zle_trans _ _ _ H1 Hx6).
omega.
apply Zle_trans with (2 := H2).
exact (digits_pow2 _ _ Hx7).
destruct (Zle_or_lt d1 (Fexp f2)).
exists f2.
exact (conj (sym_eq Hx3) (conj  H Hx4)).
exists f1.
split.
exact (sym_eq Hx1).
split.
exact Hx2.
apply Zle_lt_trans with (2 := Hx4).
cutrewrite (Fnum f2 = shl (Fnum f1) (pos_of_Z (Fexp f1 - Fexp f2))).
unfold shl.
case (Fnum f1) ; intros.
apply Zle_refl.
rewrite shift_pos_nat.
induction (nat_of_P (pos_of_Z (Fexp f1 - Fexp f2))).
apply Zle_refl.
apply Zle_trans with (1 := IHn).
unfold shift_nat.
simpl.
rewrite Zpos_xO.
generalize (Zgt_pos_0 (iter_nat n positive xO p)).
omega.
rewrite shift_pos_nat.
induction (nat_of_P (pos_of_Z (Fexp f1 - Fexp f2))).
apply Zle_refl.
apply Zle_trans with (1 := IHn).
unfold shift_nat.
simpl.
rewrite Zpos_xO.
generalize (Zgt_pos_0 (iter_nat n positive xO p)).
omega.
generalize (float2_shl_correct f1 (pos_of_Z (Fexp f1 - Fexp f2))).
rewrite <- Zpos_pos_of_Z.
2: omega.
ring (Fexp f1 - (Fexp f1 - Fexp f2))%Z.
rewrite Hx1.
rewrite <- Hx3.
clear H H2 H1 H3 Hx4 Hx3 Hx2 Hx1 p2 p1 d2 d1 xi x rdir.
induction f2.
simpl.
intro H.
apply sym_eq.
exact (float2_binade_eq_reg _ _ _ H).
Qed.

Definition round_helper (rnd : float2 -> float2) (xi zi : FF) :=
 Fle2 (lower zi) (rnd (lower xi)) &&
 Fle2 (rnd (upper xi)) (upper zi).

Theorem float_round :
 forall rdir : round_dir, forall p : positive, forall d : Z,
 forall x : R, forall xi zi : FF,
 BND x xi ->
 round_helper (round rdir (float_shift p d)) xi zi = true ->
 BND (rounding_float rdir p d x) zi.
intros rdir p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite <- (round_extension_float2 rdir _ (good_shift p d)). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite <- (round_extension_float2 rdir _ (good_shift p d)). clear H2. intro H2.
unfold rounding_float.
split.
apply Rle_trans with (1 := H1).
apply round_extension_monotone.
exact (proj1 Hx).
apply Rle_trans with (2 := H2).
apply round_extension_monotone.
exact (proj2 Hx).
Qed.

Definition enforce_helper (p : positive) (d : Z) (xi zi : FF) :=
 Fle2 (lower zi) (round roundUP (float_shift p d) (lower xi)) &&
 Fle2 (round roundDN (float_shift p d) (upper xi)) (upper zi).

Theorem float_enforce :
 forall rdir : round_dir, forall p : positive, forall d : Z,
 forall x : R, forall xi zi : FF,
 BND (rounding_float rdir p d x) xi ->
 enforce_helper p d xi zi = true ->
 BND (rounding_float rdir p d x) zi.
intros rdir p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite <- (round_extension_float2 roundUP _ (good_shift p d)). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite <- (round_extension_float2 roundDN _ (good_shift p d)). clear H2. intro H2.
destruct (representable_round_extension rdir _ (good_shift p d) x) as (m,(e,(H3,H4))).
unfold rounding_float in *.
rewrite H3.
rewrite H3 in Hx.
split.
apply Rle_trans with (1 := H1).
rewrite <- (round_extension_representable roundUP _ (good_shift p d) (Float2 m e) H4).
apply round_extension_monotone.
exact (proj1 Hx).
apply Rle_trans with (2 := H2).
rewrite <- (round_extension_representable roundDN _ (good_shift p d) (Float2 m e) H4).
apply round_extension_monotone.
exact (proj2 Hx).
Qed.

End Gappa_float.
