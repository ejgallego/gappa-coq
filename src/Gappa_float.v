Require Import Bool.
Require Import ZArith.
Require Import Reals.
Require Import Fcore.
Require Import Fcalc_digits.
Require Import Fprop_relative.
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
  forall p m, good_rexp (float_shift p m).
Proof.
intros p m.
now apply FLT_exp_correct.
Qed.

Definition rounding_float (rdir : round_dir) (p : positive) (d : Z) :=
 round_extension rdir (float_shift p d) (good_shift p d).

Definition float_ulp (p : positive) (d m e : Z) :=
 match m with
 | Zpos n => float_shift p d (e + Zpos (digits n))%Z
 | Zneg n => float_shift p d (e + Zpos (digits n))%Z
 | Z0 => (-d)%Z
 end.

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
  forall p d k x,
  (Rabs x < bpow radix2 k)%R ->
  (Rabs (rounding_float roundNE p d x - x) <= bpow radix2 (float_shift p d k - 1))%R.
Proof.
intros p d k x Hx.
unfold rounding_float.
rewrite round_extension_conversion.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, rounding_0, Rminus_0_r, Rabs_R0.
apply bpow_ge_0.
rewrite (rounding_ext _ _ _ ZrndNE) with (1 := roundNE_NE).
apply Rle_trans with (/2 * ulp radix2 (float_shift p d) x)%R.
apply ulp_half_error.
apply good_shift.
unfold ulp.
rewrite <- (bpow_add radix2 (-1)).
apply -> bpow_le.
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply Zplus_le_compat_l.
unfold canonic_exponent, float_shift.
cut (projT1 (ln_beta radix2 x) <= k)%Z.
generalize (Zmax_spec (projT1 (ln_beta radix2 x) - Zpos p) (-d)) (Zmax_spec (k - Zpos p) (-d)).
omega.
destruct (ln_beta radix2 x) as (e, He).
simpl.
specialize (He Hx0).
apply bpow_lt_bpow with radix2.
now apply Rle_lt_trans with (Rabs x).
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
  forall p d x,
  (bpow radix2 (-d + Zpos p - 1) <= Rabs x)%R ->
  (Rabs ((rounding_float roundNE p d x - x) / x) <= bpow radix2 (-Zpos p))%R.
Proof.
intros p d x Hx.
assert (Hx0: x <> R0).
intros Hx0.
apply Rle_not_lt with (1 := Hx).
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
unfold rounding_float.
rewrite round_extension_conversion.
destruct (relative_error_N_FLT_ex radix2 (-d) (Zpos p) (refl_equal _) (fun m => negb (Zeven (Zfloor m))) x Hx) as (eps, (Hr1, Hr2)).
change (float_shift p d) with (FLT_exp (-d) (Zpos p)).
rewrite (rounding_ext _ _ _ ZrndNE) with (1 := roundNE_NE).
unfold ZrndNE.
rewrite Hr2.
replace ((x * (1 + eps) - x) / x)%R with eps by now field.
revert Hr1.
rewrite <- (bpow_add radix2 (-1)%Z).
now rewrite (Zplus_comm (- Zpos p)), Zplus_assoc.
Qed.

Theorem fix_of_float :
  forall rdir x p k1 k2,
  Zle_bool k2 (-k1) = true ->
  FIX (rounding_float rdir p k1 x) k2.
Proof.
intros rdir x p k1 k2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX, rounding_float.
rewrite round_extension_conversion.
unfold rounding.
rewrite <- float2_float.
eexists ; repeat split.
simpl.
unfold canonic_exponent, float_shift.
apply Zle_trans with (1 := H).
apply Zle_max_r.
Qed.

Theorem flt_of_float :
  forall rdir x p1 p2 k,
  Zle_bool (Zpos p1) (Zpos p2) = true ->
  FLT (rounding_float rdir p1 k x) p2.
Proof.
intros rdir x p1 p2 k H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FLT, rounding_float.
rewrite round_extension_conversion.
destruct (proj2 (FLT_format_generic radix2 (-k) (Zpos p1) (refl_equal _) (rounding radix2 (float_shift p1 k) (ZrndG rdir) x)))
  as ((m, e), (H1, (H2, _))).
apply generic_format_rounding.
now apply FLT_exp_correct.
rewrite H1.
rewrite <- float2_float.
eexists ; repeat split.
apply Zlt_le_trans with (1 := H2).
change (Zpower_pos 2 p2) with (Zpower (radix_val radix2) (Zpos p2)).
apply le_Z2R.
rewrite 2!Z2R_Zpower ; try easy.
now apply -> bpow_le.
Qed.

Theorem float_of_fix_flt :
  forall rdir : round_dir,
  forall x : R, forall xi : FF,
  forall d1 d2 : Z, forall p1 p2 : positive,
  FIX x d1 -> FLT x p1 ->
  Zle_bool (-d2) d1 && Zle_bool (Zpos p1) (Zpos p2) && contains_zero_helper xi = true ->
  BND (rounding_float rdir p2 d2 x - x) xi.
Proof.
intros rdir x xi d1 d2 p1 p2 (f1,(Hx1,Hx2)) (f2,(Hx3,Hx4)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
cutrewrite (rounding_float rdir p2 d2 x = x :>R).
unfold Rminus.
rewrite (Rplus_opp_r x).
apply contains_zero with (1 := H3).
unfold rounding_float.
rewrite round_extension_conversion.
apply rounding_generic.
destruct f1 as (m1, e1).
destruct f2 as (m2, e2).
destruct (Z_eq_dec m2 0) as [Hm|Hm].
rewrite <- Hx3.
rewrite float2_float.
rewrite Hm, F2R_0.
apply generic_format_0.
assert (projT1 (ln_beta radix2 (Fcore_defs.F2R (Float radix2 m2 e2))) <= Zpos p2 + e2)%Z.
rewrite ln_beta_F2R with (1 := Hm).
apply Zplus_le_compat_r.
apply Zle_trans with (2 := H2).
apply bpow_lt_bpow with radix2.
destruct (ln_beta radix2 (Z2R m2)) as (n2, Hn).
simpl.
specialize (Hn (Z2R_neq _ _ Hm)).
apply Rle_lt_trans with (1 := proj1 Hn).
rewrite <- abs_Z2R.
now apply Z2R_lt.
destruct (Zle_or_lt e1 e2) as [He|He].
(* *)
rewrite <- Hx3.
rewrite float2_float.
apply generic_format_canonic_exponent.
apply Zmax_lub.
omega.
apply Zle_trans with (1 := H1).
now apply Zle_trans with e1.
(* *)
rewrite <- Hx1.
rewrite float2_float.
apply generic_format_canonic_exponent.
apply Zmax_lub.
rewrite <- float2_float.
rewrite Hx1, <- Hx3.
rewrite float2_float.
omega.
now apply Zle_trans with d1.
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
Proof.
intros rdir p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite rndG_conversion. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite rndG_conversion. clear H2. intro H2.
revert Hx.
unfold rounding_float.
rewrite round_extension_conversion.
intros (Hx1, Hx2).
split.
apply Rle_trans with (1 := H1).
rewrite <- (rounding_generic _ _ (ZrndG roundUP) _ (generic_format_rounding radix2 _ (good_shift p d) (ZrndG rdir) x)).
apply rounding_monotone.
apply good_shift.
exact Hx1.
apply Rle_trans with (2 := H2).
rewrite <- (rounding_generic _ _ (ZrndG roundDN) _ (generic_format_rounding radix2 _ (good_shift p d) (ZrndG rdir) x)).
apply rounding_monotone.
apply good_shift.
exact Hx2.
Qed.

Definition float_absolute_ne_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 1)%Z in
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_ne :
  forall p d x xi zi,
  ABS x xi ->
  float_absolute_ne_helper p d xi zi = true ->
  BND (rounding_float roundNE p d x - x) zi.
Proof.
intros p d x xi zi Hx Hb.
assert (H: (Rabs (rounding_float roundNE p d x - x) <= bpow radix2 (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 1))%R).
(* *)
unfold rounding_float.
rewrite round_extension_conversion.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, rounding_0, Rminus_0_r, Rabs_R0.
apply bpow_ge_0.
rewrite (rounding_ext _ _ _ ZrndNE) with (1 := roundNE_NE).
replace (bpow radix2 (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 1)) with (/2 * ulp radix2 (float_shift p d) (upper xi))%R.
(* . *)
apply Rle_trans with (/2 * ulp radix2 (float_shift p d) x)%R.
apply ulp_half_error.
apply good_shift.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply (Z2R_lt 0 2).
rewrite <- ulp_abs.
apply ulp_monotone.
clear.
intros m n H.
unfold float_shift.
generalize (Zmax_spec (m - Zpos p) (- d)) (Zmax_spec (n - Zpos p) (- d)).
omega.
now apply Rabs_pos_lt.
apply Hx.
(* . *)
unfold ulp.
rewrite <- (bpow_add radix2 (-1)).
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply (f_equal (fun e => bpow radix2 (-1 + e))).
assert (Hm0: (Fnum (upper xi)) <> Z0).
assert (Hx1 := Rabs_no_R0 _ Hx0).
contradict Hx1.
apply Rle_antisym.
replace R0 with (float2R (upper xi)).
apply Hx.
clear -Hx1.
destruct (upper xi).
simpl in Hx1.
rewrite Hx1.
apply float2_zero.
apply Rabs_pos.
clear -Hm0.
destruct (upper xi) as (m, e).
rewrite float2_float.
unfold canonic_exponent.
rewrite ln_beta_F2R with (1 := Hm0).
rewrite <- digits_ln_beta with (1 := Hm0).
simpl.
rewrite <- digits_abs.
rewrite Zplus_comm.
destruct m as [|m|m] ; unfold Zabs.
now elim Hm0.
now rewrite <- digits2_digits.
now rewrite <- digits2_digits.
(* *)
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
rewrite float2_float.
rewrite <- (opp_F2R _ 1%Z).
rewrite F2R_bpow.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply (Rle_trans _ _ _ (Rabs_idem _)).
now rewrite Rabs_Ropp.
apply Rle_trans with (2 := H2).
rewrite float2_float.
rewrite F2R_bpow.
now apply (Rle_trans _ _ _ (Rabs_idem _)).
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
rewrite float2_float, F2R_bpow.
apply float_absolute_ne_whole.
now rewrite <- F2R_bpow, <- float2_float.
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
  forall p d x xi zi,
  ABS x xi ->
  float_relative_ne_helper p d xi zi = true ->
  REL (rounding_float roundNE p d x) x zi.
Proof.
intros p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite float2_float, F2R_bpow. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite float2_float, <- (opp_F2R _ 1%Z), F2R_bpow. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite float2_float, F2R_bpow. clear H3. intro H3.
exists ((rounding_float roundNE p d x - x) / x)%R.
split.
assert (Rabs ((rounding_float roundNE p d x - x) / x) <= bpow radix2 (- Zpos p))%R.
apply float_relative_ne_whole.
apply Rle_trans with (1 := H1).
apply Hx.
split.
apply Rle_trans with (1 := H2).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (2 := H).
rewrite <- Rabs_Ropp.
apply Rabs_idem.
apply Rle_trans with (2 := H3).
apply Rle_trans with (2 := H).
apply Rabs_idem.
field.
intros H.
apply Rle_not_lt with (1 := H1).
apply Rle_lt_trans with (1 := proj1 (proj2 Hx)).
rewrite H, Rabs_R0.
apply bpow_gt_0.
Qed.

Definition rel_of_fix_float_ne_helper (p : positive) (d xn : Z) (zi : FF) :=
 Zle_bool (-d) xn &&
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem rel_of_fix_float_ne :
  forall p d xn x zi,
  FIX x xn ->
  rel_of_fix_float_ne_helper p d xn zi = true ->
  REL (rounding_float roundNE p d x) x zi.
Proof.
intros p d xn x zi ((mx, ex), (Hx1, Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite float2_float, <- (opp_F2R _ 1%Z), F2R_bpow. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). rewrite float2_float, F2R_bpow. clear H3. intro H3.
destruct (Rle_or_lt (Rabs x) (bpow radix2 (- d + Zpos p))) as [He|He].
(* *)
unfold rounding_float.
rewrite round_extension_conversion.
rewrite rounding_generic.
exists R0.
repeat split.
apply Rle_trans with (1 := H2).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply bpow_ge_0.
apply Rle_trans with (2 := H3).
apply bpow_ge_0.
now rewrite Rplus_0_r, Rmult_1_r.
apply <- FLT_generic_format_FIX ; try easy.
rewrite <- Hx1.
rewrite float2_float.
apply generic_format_canonic_exponent.
now apply Zle_trans with xn.
(* *)
exists ((rounding_float roundNE p d x - x) / x)%R.
assert (Rabs ((rounding_float roundNE p d x - x) / x) <= bpow radix2 (- Zpos p))%R.
apply float_relative_ne_whole.
apply Rlt_le.
apply Rlt_trans with (2 := He).
apply -> bpow_lt.
pattern (-d + Zpos p)%Z at 2 ; rewrite <- Zplus_0_r.
now apply Zplus_lt_compat_l.
repeat split.
apply Rle_trans with (1 := H2).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (2 := H).
rewrite <- Rabs_Ropp.
apply Rabs_idem.
apply Rle_trans with (2 := H3).
apply Rle_trans with (2 := H).
apply Rabs_idem.
field.
intros H0.
apply Rlt_not_le with (1 := He).
rewrite H0, Rabs_R0.
apply bpow_ge_0.
Qed.

End Gappa_float.
