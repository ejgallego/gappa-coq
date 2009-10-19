Require Import Bool.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_integer.
Require Import Gappa_pred_bnd.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.
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

Definition float_ulp (p : positive) (d m e : Z) :=
 match m with
 | Zpos n => float_shift p d (e + Zpos (digits n))%Z
 | Zneg n => float_shift p d (e + Zpos (digits n))%Z
 | Z0 => (-d)%Z
 end.

Lemma float_absolute_ne_binade :
 forall p : positive, forall d k : Z, forall x : R,
 (Float2 1 (k - 1) <= x < Float2 1 k)%R ->
 (Rabs (rounding_float roundNE p d x - x) <= Float2 1 (float_shift p d k - 1))%R.
intros p d k x Hx.
assert (0 < x)%R.
apply Rlt_le_trans with (2 := proj1 Hx).
apply float2_pos_compat.
exact (refl_equal _).
unfold rounding_float.
destruct (rexp_case_real _ (good_shift p d) _ H) as [(k0,(H0,H1))|(e,(m,(H0,H1)))].
(* *)
assert (k0 = -d)%Z.
unfold float_shift in H0.
destruct (Zmax_irreducible_inf (k0 - Zpos p) (-d)) as [H2|H2].
generalize (Zgt_pos_0 p).
omega.
rewrite H0 in H2.
exact H2.
rewrite H2 in H1.
rewrite H2 in H0.
clear H2 k0.
cutrewrite (float_shift p d k = -d)%Z.
destruct (Rle_or_lt x (Float2 1 (-d - 1))).
cutrewrite (round_extension roundNE (float_shift p d) (good_shift p d) x = 0 :>R)%R.
rewrite Rminus_0_l.
rewrite Rabs_Ropp.
rewrite Rabs_right.
2: left ; exact H.
exact H2.
apply Rle_antisym.
2: apply round_extension_positive with (1 := H).
cutrewrite (R0 = round_extension roundNE (float_shift p d) (good_shift p d) (Float2 1 (-d - 1))).
apply round_extension_monotone.
exact H2.
rewrite round_extension_float2.
unfold round, round_pos. simpl.
cutrewrite (-d - 1 + 1 = -d)%Z. 2: ring.
rewrite H0.
cutrewrite (-d - (-d - 1) = 1)%Z. 2: ring.
simpl.
rewrite float2_zero.
exact (refl_equal _).
cutrewrite (round_extension roundNE (float_shift p d) (good_shift p d) x = Float2 1 (-d) :>R).
rewrite Rabs_right.
apply Rle_trans with (Float2 1 (-d) - Float2 1 (-d - 1))%R.
unfold Rminus.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
exact (Rlt_le _ _ H2).
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
simpl.
cutrewrite (-d - (-d - 1) = 1)%Z. 2: ring.
apply Rle_refl.
apply Rgt_ge.
apply Rgt_minus.
exact H1.
destruct (round_extension_prop_pos roundNE _ (good_shift p d) _ H) as (m1,(m2,(e1,(e2,(H4,(H5,(H6,(H7,H8)))))))).
destruct (Rle_or_lt (Float2 1 (-d)) (Float2 (Zpos m2) e2)).
rewrite <- (round_extension_representable roundNE _ (good_shift p d) (Float2 1 (-d))).
apply Rle_antisym.
apply round_extension_monotone.
exact (Rlt_le _ _ H1).
rewrite H6.
rewrite <- (round_extension_float2 roundNE _ (good_shift p d)).
apply round_extension_monotone.
exact H3.
simpl.
unfold float_shift.
apply Zmax_lub.
2: apply Zle_refl.
generalize (Zgt_pos_0 p).
omega.
rewrite H6.
unfold round. simpl.
rewrite (proj2 (proj2 (round_constant_underflow rndNE _ (good_shift p d) _ H0 m2 e2)) (conj (Rlt_le_trans _ _ _ H2 (proj2 H4)) H3)).
simpl.
exact (refl_equal _).
unfold float_shift.
apply Zle_antisym.
2: apply Zmax2.
assert (k - 1 < -d)%Z.
apply float2_pow2_lt.
exact (Rle_lt_trans _ _ _ (proj1 Hx) H1).
assert (k - Zpos p < -d)%Z.
generalize (Zgt_pos_0 p).
omega.
unfold Zmax.
rewrite H3.
apply Zle_refl.
(* *)
cutrewrite (float_shift p d k = e).
destruct (round_extension_prop_pos roundNE _ (good_shift p d) _ H) as (m1,(m2,(e1,(e2,(H4,(H5,(H6,(H7,H8)))))))).
destruct (total_order_T (Float2 (Zpos m * 2 + 1) (e - 1)) x) as [[H2|H2]|H2].
cutrewrite (round_extension roundNE (float_shift p d) (good_shift p d) x = Float2 (Zpos m + 1) e :>R).
rewrite Rabs_right.
apply Rle_trans with (Float2 (Zpos m + 1) e - Float2 (Zpos m * 2 + 1) (e - 1))%R.
unfold Rminus.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
exact (Rlt_le _ _ H2).
rewrite (float2_shift_m1 e).
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
rewrite Zminus_diag.
unfold Fnum, Fexp.
cutrewrite ((Zpos m + 1) * 2 - (Zpos m * 2 + 1) = 1)%Z. 2: ring.
apply Rle_refl.
apply Rgt_ge.
apply Rgt_minus.
exact (proj2 H1).
destruct (Rle_or_lt (Float2 (Zpos m + 1) e) (Float2 (Zpos m2) e2)).
destruct (rexp_succ _ (good_shift p d) _ _ (Zeq_le _ _ H0)) as (m3,(e3,(HA,HB))).
rewrite <- HA.
rewrite <- (round_extension_representable roundNE _ (good_shift p d) (Float2 (Zpos m3) e3) HB).
apply Rle_antisym.
apply round_extension_monotone.
rewrite HA.
exact (Rlt_le _ _ (proj2 H1)).
rewrite H6.
rewrite <- (round_extension_float2 roundNE _ (good_shift p d)).
apply round_extension_monotone.
rewrite HA.
exact H3.
rewrite H6.
unfold round. simpl.
rewrite (proj2 (proj2 (round_constant rndNE _ _ _ H0 m2 e2)) (conj (Rlt_le_trans _ _ _ H2 (proj2 H4)) H3)).
simpl.
rewrite Pplus_one_succ_r.
exact (refl_equal _).
rewrite <- H2.
rewrite round_extension_float2.
unfold round. simpl.
rewrite tofloat_0.
rewrite <- H2 in H1.
assert (H9 := round_bound_local _ _ rndNE_good _ _ H0 _ _ H1).
destruct (Rle_or_lt R0 (tofloat (round_pos rndNE (float_shift p d) (m * 2 + 1) (e - 1)) - Float2 (Zpos m * 2 + 1) (e - 1))) as [HA|HA].
rewrite Rabs_right.
2: exact (Rle_ge _ _ HA).
apply Rle_trans with (Float2 (Zpos m + 1) e - Float2 (Zpos (m * 2 + 1)) (e - 1))%R.
unfold Rminus.
apply Rplus_le_compat_r.
exact (proj2 H9).
rewrite (float2_shift_m1 e).
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
rewrite Zminus_diag.
unfold Fnum, Fexp.
change (Zpos (m * 2 + 1)) with (Zpos m * 2 + 1)%Z.
cutrewrite ((Zpos m + 1) * 2 - (Zpos m * 2 + 1) = 1)%Z. 2: ring.
apply Rle_refl.
rewrite Rabs_left.
2: exact HA.
rewrite Ropp_minus_distr.
apply Rle_trans with (Float2 (Zpos (m * 2 + 1)) (e - 1) - Float2 (Zpos m) e)%R.
unfold Rminus.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
exact (proj1 H9).
rewrite (float2_shift_m1 e).
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
rewrite Zminus_diag.
unfold Fnum, Fexp.
change (Zpos (m * 2 + 1)) with (Zpos m * 2 + 1)%Z.
cutrewrite (Zpos m * 2 + 1 - Zpos m * 2 = 1)%Z. 2: ring.
apply Rle_refl.
destruct (Rle_or_lt x (Float2 (Zpos m) e)) as [H9|H9].
rewrite (Rle_antisym _ _ H9 (proj1 H1)).
rewrite round_extension_representable.
rewrite Rminus_diag_eq. 2: apply refl_equal.
rewrite Rabs_R0.
apply Rlt_le.
apply float2_pos_compat.
exact (refl_equal _).
exact (Zeq_le _ _ H0).
cutrewrite (round_extension roundNE (float_shift p d) (good_shift p d) x = Float2 (Zpos m) e :>R).
rewrite Rabs_left.
rewrite Ropp_minus_distr.
apply Rle_trans with (Float2 (Zpos m * 2 + 1) (e - 1) - Float2 (Zpos m) e)%R.
unfold Rminus.
apply Rplus_le_compat_r.
exact (Rlt_le _ _ H2).
rewrite (float2_shift_m1 e).
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
rewrite Zminus_diag.
unfold Fnum, Fexp.
cutrewrite (Zpos m * 2 + 1 - Zpos m * 2 = 1)%Z. 2: ring.
apply Rle_refl.
apply Rlt_minus.
exact H9.
destruct (Rle_or_lt (Float2 (Zpos m1) e1) (Float2 (Zpos m) e)).
rewrite <- (round_extension_representable roundNE _ (good_shift p d) (Float2 (Zpos m) e)).
apply Rle_antisym.
rewrite H5.
rewrite <- (round_extension_float2 roundNE _ (good_shift p d)).
apply round_extension_monotone.
exact H3.
apply round_extension_monotone.
exact (proj1 H1).
exact (Zeq_le _ _ H0).
rewrite H5.
unfold round. simpl.
rewrite ((proj1 (round_constant rndNE _ _ _ H0 m1 e1)) (conj H3 (Rle_lt_trans _ _ _ (proj1 H4) H2))).
exact (refl_equal _).
cutrewrite (k = e + Zpos (digits m))%Z.
exact H0.
assert (H2 := float2_digits_correct m e).
apply Zle_antisym.
assert (k - 1 < e + Zpos (digits m))%Z. 2: omega.
apply float2_pow2_lt.
apply Rle_lt_trans with (1 := proj1 Hx).
apply Rlt_le_trans with (1 := proj2 H1).
fold (Zsucc (Zpos m)).
rewrite <- Zpos_succ_morphism.
destruct (digits_succ m) as [H3|(H3,H4)].
rewrite <- H3.
apply Rlt_le.
exact (proj2 (float2_digits_correct (Psucc m) e)).
rewrite H4.
rewrite <- (float2_shl_correct 1 (e + Zpos (digits m)) (digits m)).
simpl.
cutrewrite (e + Zpos (digits m) - Zpos (digits m) = e)%Z. 2: ring.
unfold shift_pos.
apply Rle_refl.
apply float2_repartition_underflow.
exact (Rle_lt_trans _ _ _ (proj1 H1) (proj2 Hx)).
Qed.

Lemma float_absolute_ne_sym :
 forall p : positive, forall d : Z, forall x : R,
 (Rabs (rounding_float roundNE p d x - x) = Rabs (rounding_float roundNE p d (Rabs x) - Rabs x))%R.
intros p d x.
unfold rounding_float.
destruct (Rle_or_lt 0 x) as [H|H].
rewrite (Rabs_right _ (Rle_ge _ _ H)).
exact (refl_equal _).
rewrite (Rabs_left _ H).
rewrite round_extension_opp.
simpl.
fold roundNE.
unfold Rminus.
rewrite <- Ropp_plus_distr.
rewrite Rabs_Ropp.
exact (refl_equal _).
Qed.

Lemma float_absolute_ne_whole :
 forall p : positive, forall d k : Z, forall x : R,
 (Rabs x < Float2 1 k)%R ->
 (Rabs (rounding_float roundNE p d x - x) <= Float2 1 (float_shift p d k - 1))%R.
intros p d k x H.
rewrite float_absolute_ne_sym.
destruct (Rabs_pos x).
destruct (log2 _ H0) as (k0,Hk).
apply Rle_trans with (Float2 1 (float_shift p d k0 - 1)).
apply float_absolute_ne_binade.
do 2 rewrite float2_pow2.
exact Hk.
apply float2_Rle_pow2.
unfold Zminus.
apply Zplus_le_compat_r.
unfold float_shift.
apply Zmax_lub.
2: apply Zmax2.
apply Zle_trans with (2 := Zmax1 (k - Zpos p) (- d)).
unfold Zminus.
apply Zplus_le_compat_r.
assert (k0 - 1 < k)%Z. 2: omega.
apply float2_pow2_lt.
rewrite float2_pow2.
apply Rle_lt_trans with (Rabs x).
exact (proj1 Hk).
exact H.
rewrite <- H0.
unfold rounding_float.
rewrite round_extension_zero.
rewrite Rminus_0_r.
rewrite Rabs_R0.
left.
apply float2_pos_compat.
exact (refl_equal _).
Qed.

Lemma Zmax_inf_l :
 forall m n : Z, (n <= m)%Z -> Zmax m n = m.
intros m n H.
generalize (Zle_ge _ _ H).
unfold Zmax, Zge.
case (m ?= n)%Z ; intros ; try exact (refl_equal _).
elim H0.
exact (refl_equal _).
Qed.

Lemma float_relative_ne_whole :
 forall p : positive, forall d : Z, forall x : R,
 (Float2 1 (-d + Zpos p - 1) <= Rabs x)%R ->
 (Rabs ((rounding_float roundNE p d x - x) / x) <= Float2 1 (-Zpos p))%R.
intros p d x Hx.
assert (H9: (x <> 0)%R).
destruct (Rle_or_lt 0 x).
rewrite (Rabs_right _ (Rle_ge _ _ H)) in Hx.
apply Rgt_not_eq.
destruct H.
exact H.
elim (Rle_not_lt _ _ Hx).
rewrite <- H.
apply float2_pos_compat.
exact (refl_equal _).
exact (Rlt_not_eq _ _ H).
unfold Rdiv.
rewrite Rabs_mult.
rewrite (Rabs_Rinv _ H9).
rewrite float_absolute_ne_sym.
apply Rmult_le_reg_l with (Rabs x).
exact (Rabs_pos_lt _ H9).
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
2: exact (Rabs_no_R0 _ H9).
destruct (log2 _ (Rabs_pos_lt _ H9)) as (k,Hk).
apply Rle_trans with (Float2 1 (float_shift p d k - 1))%R.
apply float_absolute_ne_whole.
rewrite Rabs_Rabsolu.
rewrite float2_pow2.
exact (proj2 Hk).
unfold float_shift.
rewrite Zmax_inf_l.
apply Rle_trans with (Float2 1 (k - 1) * Float2 1 (- Zpos p))%R.
rewrite <- Fmult2_correct.
unfold Fmult2, Zminus.
simpl.
cutrewrite (k + Zneg p + -1 = k + -1 + Zneg p)%Z. 2: ring.
apply Rle_refl.
apply Rmult_le_compat_r.
apply Rlt_le.
apply float2_pos_compat.
exact (refl_equal _).
rewrite float2_pow2.
exact (proj1 Hk).
assert (-d + Zpos p - 1 < k)%Z. 2: omega.
apply float2_pow2_lt.
apply Rle_lt_trans with (1 := Hx).
rewrite float2_pow2.
exact (proj2 Hk).
Qed.

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
repeat rewrite float2_zero.
exact (refl_equal _).
exact (Zle_refl _).
exists (Float2 (Zpos p0) e).
split.
exact (sym_eq H1).
apply Zle_trans with (1 := H).
unfold rexp_representable, float_shift in H2.
apply Zle_trans with (2 := H2).
exact (Zmax2 _ _).
exists (Float2 (Zneg p0) e).
split.
exact (sym_eq H1).
apply Zle_trans with (1 := H).
unfold rexp_representable, float_shift in H2.
apply Zle_trans with (2 := H2).
exact (Zmax2 _ _).
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
change 2%Z with (Z_of_nat 2).
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite <- Z2R_IZR.
apply Rlt_le_trans with (1 := proj2 (digits_correct p)).
assert (Float2 1 (Zpos (digits p)) <= Float2 1 (Zpos p2))%R.
apply Rle_trans with (2 := float2_Rle_pow2 _ _ H).
apply float2_Rle_pow2.
generalize (Zmax1 (e + Zpos (digits p) - Zpos p1) (- k)).
omega.
do 2 rewrite <- float2_pow2.
exact H0.
simpl.
apply lt_IZR.
rewrite Zpower_pos_nat.
change 2%Z with (Z_of_nat 2).
rewrite Zpower_nat_powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite <- Z2R_IZR.
apply Rlt_le_trans with (1 := proj2 (digits_correct p)).
assert (Float2 1 (Zpos (digits p)) <= Float2 1 (Zpos p2))%R.
apply Rle_trans with (2 := float2_Rle_pow2 _ _ H).
apply float2_Rle_pow2.
generalize (Zmax1 (e + Zpos (digits p) - Zpos p1) (- k)).
omega.
do 2 rewrite <- float2_pow2.
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
rewrite float2_zero.
apply round_zero.
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
generalize (float2_shl_correct (Fnum f1) (Fexp f1) (pos_of_Z (Fexp f1 - Fexp f2))).
rewrite Zpos_pos_of_Z_minus.
2: omega.
cutrewrite (Fexp f1 - (Fexp f1 - Fexp f2) = Fexp f2)%Z. 2: ring.
induction f1.
simpl.
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

Definition float_absolute_ne_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 1)%Z in
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS x xi ->
 float_absolute_ne_helper p d xi zi = true ->
 BND (rounding_float roundNE p d x - x) zi.
intros p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
set (e := (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 1)%Z) in H1, H2.
cutrewrite (Float2 (-1) e = -Float2 1 e:>R)%R in H1.
2: intros ; rewrite <- Fopp2_correct ; apply refl_equal.
cut (Rabs (rounding_float roundNE p d x - x) <= Float2 1 e)%R.
split.
apply Rle_trans with (1 := H1).
rewrite <- (Ropp_involutive (rounding_float roundNE p d x - x)%R).
apply Ropp_le_contravar.
apply Rle_trans with (Rabs (- (rounding_float roundNE p d x - x))%R).
apply RRle_abs.
rewrite Rabs_Ropp.
exact H.
apply Rle_trans with (2 := H2).
apply Rle_trans with (Rabs (rounding_float roundNE p d x - x)%R).
apply RRle_abs.
exact H.
destruct Hx as (_,(_,Hx)).
unfold e.
clear H1 H2 zi e.
induction (upper xi).
induction Fnum ; simpl.
cutrewrite (x = R0).
unfold rounding_float.
rewrite round_extension_zero.
rewrite Rminus_0_r.
rewrite Rabs_R0.
left.
apply float2_pos_compat.
exact (refl_equal _).
elim (Req_dec x 0) ; intro H.
exact H.
elim Rlt_not_le with (2 := Hx).
rewrite float2_zero.
apply Rabs_pos_lt with (1 := H).
apply float_absolute_ne_whole.
apply Rle_lt_trans with (1 := Hx).
exact (proj2 (float2_digits_correct _ _)).
elim Rlt_not_le with (2 := Hx).
apply Rlt_le_trans with (Float2 0 Fexp).
apply float2_binade_lt.
apply Zlt_neg_0.
rewrite float2_zero.
apply Rabs_pos.
Qed.

Definition float_absolute_wide_ne_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 2)%Z in
 Zle_bool (-d) (Fexp u - Zpos p) &&
 Fle2 u (Float2 (Zpos (xI (shift_pos p xH))) e) &&
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_wide_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS x xi ->
 float_absolute_wide_ne_helper p d xi zi = true ->
 BND (rounding_float roundNE p d x - x) zi.
intros p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). clear H4. intro H4.
set (e := (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 2)%Z) in H2, H3, H4.
cutrewrite (Float2 (-1) e = -Float2 1 e:>R)%R in H3.
2: intros ; rewrite <- Fopp2_correct ; apply refl_equal.
cut (Rabs (rounding_float roundNE p d x - x) <= Float2 1 e)%R.
split.
apply Rle_trans with (1 := H3).
rewrite <- (Ropp_involutive (rounding_float roundNE p d x - x)%R).
apply Ropp_le_contravar.
apply Rle_trans with (Rabs (- (rounding_float roundNE p d x - x))%R).
apply RRle_abs.
rewrite Rabs_Ropp.
exact H.
apply Rle_trans with (2 := H4).
apply Rle_trans with (Rabs (rounding_float roundNE p d x - x)%R).
apply RRle_abs.
exact H.
destruct Hx as (_,(_,Hx)).
clear H3 H4 zi.
induction (upper xi).
induction Fnum ; simpl.
cutrewrite (x = R0).
unfold rounding_float.
rewrite round_extension_zero.
rewrite Rminus_0_r.
rewrite Rabs_R0.
left.
apply float2_pos_compat.
exact (refl_equal _).
elim (Req_dec x 0) ; intro H.
exact H.
elim Rlt_not_le with (2 := Hx).
rewrite float2_zero.
apply Rabs_pos_lt with (1 := H).
simpl in e, H1.
assert (H9: (e = Fexp + Zpos (digits p0) - Zpos p - 2)%Z).
unfold e, float_shift.
rewrite Zmax_inf_l.
exact (refl_equal _).
generalize (Zgt_pos_0 (digits p0)).
omega.
destruct (Rle_or_lt (Float2 1 (Fexp + Zpos (digits p0) - 1)%Z) (Rabs x)).
rewrite float_absolute_ne_sym.
cutrewrite (rounding_float roundNE p d (Rabs x) = Float2 1 (Fexp + Zpos (digits p0) - 1) :>R).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rle_trans with (Float2 (Zpos (xI (shift_pos p 1))) e - Float2 1 (Fexp + Zpos (digits p0) - 1))%R.
unfold Rminus.
apply Rplus_le_compat_r.
exact (Rle_trans _ _ _ Hx H2).
rewrite H9.
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
simpl.
clear H H9 H2 e H1 Hx xi x d.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p - 2 - (Fexp + Zpos (digits p0) - 1) = Zneg (p + 1))%Z.
cutrewrite (Zpos (xI (shift_pos p 1)) - Zpos (shift_pos (p + 1) 1) = 1)%Z.
apply Rle_refl.
unfold shift_pos.
repeat rewrite iter_nat_of_P.
rewrite <- Pplus_one_succ_r.
rewrite nat_of_P_succ_morphism.
simpl (iter_nat (S (nat_of_P p)) positive xO xH).
rewrite Zpos_xO.
rewrite Zpos_xI.
ring.
rewrite Zneg_plus_distr.
rewrite <- (Zopp_neg p).
ring.
apply Rle_trans with (Rabs x - Rabs x)%R.
unfold Rminus.
apply Rplus_le_compat_r.
exact H.
rewrite Rminus_diag_eq.
apply Rle_refl.
exact (refl_equal _).
unfold rounding_float.
apply Rle_antisym.
cutrewrite (Float2 1 (Fexp + Zpos (digits p0) - 1) =
  round_extension roundNE (float_shift p d) (good_shift p d) (Float2 (Zpos (xI (shift_pos p 1))) e) :>R).
apply round_extension_monotone.
exact (Rle_trans _ _ _ Hx H2).
rewrite round_extension_float2.
unfold round, round_pos.
simpl.
cutrewrite (float_shift p d (e + Zpos (Psucc (digits (shift_pos p 1)))) = e + 2)%Z.
cutrewrite (e + 2 - e = 2)%Z. 2: ring.
unfold shr, shr_aux, shift_pos.
simpl.
rewrite iter_nat_of_P.
destruct (ZL4 p) as (p1,H3).
rewrite H3.
simpl.
rewrite H9.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p - 2 + 2 = Fexp + Zpos (digits p0) - Zpos p)%Z.
2: ring.
destruct (Psucc_pred p) as [H4|H4].
rewrite H4.
rewrite H4 in H3.
injection H3.
intro H5.
rewrite <- H5.
exact (refl_equal _).
rewrite <- (float2_shl_correct 1 (Fexp + Zpos (digits p0) - 1)%Z (Ppred p)).
simpl.
unfold shift_pos.
rewrite iter_nat_of_P.
rewrite <- H4 in H3.
rewrite nat_of_P_succ_morphism in H3.
injection H3.
intro H5.
rewrite H5.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p = Fexp + Zpos (digits p0) - 1 - Zpos (Ppred p))%Z.
exact (refl_equal _).
pattern p at 1 ; rewrite <- H4.
rewrite Zpos_succ_morphism.
unfold Zsucc.
ring.
rewrite H9.
cutrewrite (digits (shift_pos p 1) = Psucc p)%Z.
repeat rewrite Zpos_succ_morphism.
unfold Zsucc.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p - 2 + (Zpos p + 1 + 1) = Fexp + Zpos (digits p0))%Z. 2: ring.
unfold float_shift.
rewrite Zmax_inf_l.
ring.
generalize (Zgt_pos_0 (digits p0)).
omega.
clear H H9 H2 e H1 Hx Fexp p0 xi x d.
unfold shift_pos.
rewrite iter_nat_of_P.
rewrite <- P_of_succ_nat_o_nat_of_P_eq_succ.
induction (nat_of_P p).
exact (refl_equal _).
simpl.
rewrite IHn.
exact (refl_equal _).
rewrite <- (round_extension_representable roundNE _ (good_shift p d) (Float2 1 (Fexp + Zpos (digits p0) - 1))).
apply round_extension_monotone.
exact H.
simpl.
unfold float_shift.
rewrite Zmax_inf_l.
generalize (Zgt_pos_0 p).
omega.
generalize (Zgt_pos_0 (digits p0)).
omega.
cutrewrite (e = float_shift p d (Fexp + Zpos (digits p0) - 1) - 1)%Z.
apply float_absolute_ne_whole.
exact H.
unfold e, float_shift.
assert (H3 := Zgt_pos_0 (digits p0)).
assert (H4 := Zgt_pos_0 p).
repeat rewrite Zmax_inf_l ; omega.
elim Rlt_not_le with (2 := Hx).
apply Rlt_le_trans with (Float2 0 Fexp).
apply float2_binade_lt.
apply Zlt_neg_0.
rewrite float2_zero.
apply Rabs_pos.
Qed.

Definition float_relative_ne_helper (p : positive) (d : Z) (xi zi : FF) :=
 Fle2 (Float2 1 (-d + Zpos p - 1)) (lower xi) &&
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem float_relative_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS x xi ->
 float_relative_ne_helper p d xi zi = true ->
 REL (rounding_float roundNE p d x) x zi.
intros p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
cutrewrite (Float2 (-1) (Zneg p) = -Float2 1 (Zneg p) :>R)%R in H2.
2: intros ; rewrite <- Fopp2_correct ; apply refl_equal.
exists ((rounding_float roundNE p d x - x) / x)%R.
split.
cut (Rabs ((rounding_float roundNE p d x - x) / x) <= Float2 1 (- Zpos p))%R.
split.
apply Rle_trans with (1 := H2).
rewrite <- (Ropp_involutive ((rounding_float roundNE p d x - x) / x)%R).
apply Ropp_le_contravar.
apply Rle_trans with (Rabs (- ((rounding_float roundNE p d x - x) / x))%R).
apply RRle_abs.
rewrite Rabs_Ropp.
exact H.
apply Rle_trans with (2 := H3).
apply Rle_trans with (Rabs ((rounding_float roundNE p d x - x) / x)%R).
apply RRle_abs.
exact H.
destruct Hx as (_,(Hx,_)).
clear H2 H3 zi.
apply float_relative_ne_whole.
exact (Rle_trans _ _ _ H1 Hx).
field.
case (Rcase_abs x) ; intro.
apply Rlt_not_eq with (1 := r).
rewrite <- (Rabs_right x r).
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (2 := proj1 (proj2 Hx)).
apply Rlt_le_trans with (2 := H1).
apply float2_pos_compat.
exact (refl_equal _).
Qed.

Definition rel_of_fix_float_ne_helper (p : positive) (d xn : Z) (zi : FF) :=
 Zle_bool (-d) xn &&
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem rel_of_fix_float_ne :
 forall p : positive, forall d xn : Z, forall x : R, forall zi : FF,
 FIX x xn ->
 rel_of_fix_float_ne_helper p d xn zi = true ->
 REL (rounding_float roundNE p d x) x zi.
intros p d xn x zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
cutrewrite (Float2 (-1) (Zneg p) = -Float2 1 (Zneg p) :>R)%R in H2.
2: intros ; rewrite <- Fopp2_correct ; apply refl_equal.
case (Rle_or_lt (Float2 1 (-d + Zpos p)) (Rabs x)) ; intro H0.
exists ((rounding_float roundNE p d x - x) / x)%R.
split.
cut (Rabs ((rounding_float roundNE p d x - x) / x) <= Float2 1 (- Zpos p))%R.
split.
apply Rle_trans with (1 := H2).
rewrite <- (Ropp_involutive ((rounding_float roundNE p d x - x) / x)%R).
apply Ropp_le_contravar.
apply Rle_trans with (Rabs (- ((rounding_float roundNE p d x - x) / x))%R).
apply RRle_abs.
rewrite Rabs_Ropp.
exact H.
apply Rle_trans with (2 := H3).
apply Rle_trans with (Rabs ((rounding_float roundNE p d x - x) / x)%R).
apply RRle_abs.
exact H.
clear H2 H3 zi.
apply float_relative_ne_whole.
apply Rle_trans with (2 := H0).
rewrite (float2_shift_m1 (-d + Zpos p)).
apply float2_binade_le.
discriminate.
field.
case (Rcase_abs x) ; intro.
apply Rlt_not_eq with (1 := r).
rewrite <- (Rabs_right x r).
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (2 := H0).
apply float2_pos_compat.
exact (refl_equal _).
cutrewrite (rounding_float roundNE p d x = x :>R).
exists R0.
split.
2: ring.
split.
apply Rle_trans with (1 := H2).
apply Rge_le.
apply Ropp_0_le_ge_contravar.
apply Rlt_le.
apply float2_pos_compat.
exact (refl_equal _).
apply Rle_trans with (2 := H3).
apply Rlt_le.
apply float2_pos_compat.
exact (refl_equal _).
clear H2 H3.
cut (exists m : Z, x = Float2 m (-d)).
intros (m,H). rewrite H. rewrite H in H0. clear H.
unfold rounding_float.
rewrite round_extension_float2.
cutrewrite (Float2 1 (-d + Zpos p) = Float2 (Zpower_pos 2 p) (-d) :>R) in H0.
induction m.
rewrite float2_zero.
apply round_zero.
unfold round. simpl.
rewrite round_rexp_exact.
apply refl_equal.
unfold float_shift, Zmax.
cut (Zpos (digits p0) <= Zpos p)%Z. intro H.
case (-d + Zpos (digits p0) - Zpos p ?= - d)%Z ; omega.
apply digits_pow2.
case (Zle_or_lt (Zpower_pos 2 p) (Zpos p0)) ; intro H.
2: exact H.
elim (Rlt_not_le _ _ H0).
rewrite Rabs_right.
exact (float2_binade_le _ _ _ H).
apply Rle_ge.
apply Rlt_le.
apply float2_pos_compat.
exact (refl_equal _).
unfold round. simpl.
rewrite round_rexp_exact.
apply refl_equal.
unfold float_shift, Zmax.
cut (Zpos (digits p0) <= Zpos p)%Z. intro H.
case (-d + Zpos (digits p0) - Zpos p ?= - d)%Z ; omega.
apply digits_pow2.
case (Zle_or_lt (Zpower_pos 2 p) (Zpos p0)) ; intro H.
2: exact H.
elim (Rlt_not_le _ _ H0).
rewrite Rabs_left.
rewrite <- Fopp2_correct.
exact (float2_binade_le _ _ _ H).
cutrewrite (Float2 (Zneg p0) (-d) = -Float2 (Zpos p0) (-d) :>R)%R .
2: intros ; rewrite <- Fopp2_correct ; apply refl_equal.
apply Ropp_lt_gt_0_contravar.
unfold Rgt.
apply float2_pos_compat.
exact (refl_equal _).
rewrite <- (float2_shl_correct 1 (-d + Zpos p)%Z p).
cutrewrite (-d + Zpos p - Zpos p = -d)%Z. 2: ring.
simpl.
rewrite shift_pos_correct.
rewrite Zmult_1_r.
apply refl_equal.
destruct Hx as (x0,(Hx1,Hx2)).
rewrite <- Hx1.
clear H0 Hx1 zi x.
induction x0.
case (dec_eq Fexp (-d)%Z) ; intro H.
exists Fnum.
rewrite H.
apply refl_equal.
exists (shl Fnum (pos_of_Z (Fexp - -d)%Z)).
rewrite <- (float2_shl_correct Fnum Fexp (pos_of_Z (Fexp - - d))).
rewrite Zpos_pos_of_Z.
cutrewrite (Fexp - (Fexp - -d) = -d)%Z. 2: ring.
apply refl_equal.
simpl in Hx2.
omega.
Qed.

End Gappa_float.
