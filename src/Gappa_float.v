Require Import Bool.
Require Import ZArith.
Require Import Reals.
From Flocq Require Import Core Digits Round Relative.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_pred_bnd.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.
Require Import Gappa_round.

Global Notation rounding_float rdir p d :=
  (Generic_fmt.round radix2 (FLT_exp d (Zpos p)) rdir) (only parsing).

Global Notation rounding_floatx rdir p :=
  (Generic_fmt.round radix2 (FLX_exp (Zpos p)) rdir) (only parsing).

Definition float_ulp (p : positive) (d m e : Z) :=
 match m with
 | Zpos n => FLT_exp d (Zpos p) (e + Zpos (digits n))%Z
 | Zneg n => FLT_exp d (Zpos p) (e + Zpos (digits n))%Z
 | Z0 => d
 end.

Definition floatx_ulp (p : positive) (m e : Z) :=
 match m with
 | Zpos n => FLX_exp (Zpos p) (e + Zpos (digits n))%Z
 | Zneg n => FLX_exp (Zpos p) (e + Zpos (digits n))%Z
 | Z0 => Z0
 end.

Lemma float_absolute_ne_sym :
  forall p d x,
  (Rabs (rounding_float rndNE p d x - x) = Rabs (rounding_float rndNE p d (Rabs x) - Rabs x))%R.
Proof.
intros p d x.
destruct (Rle_or_lt 0 x) as [H|H].
rewrite (Rabs_right _ (Rle_ge _ _ H)).
exact (refl_equal _).
rewrite (Rabs_left _ H).
rewrite round_NE_opp.
unfold Rminus.
rewrite <- Ropp_plus_distr.
now rewrite Rabs_Ropp.
Qed.

Lemma floatx_absolute_ne_sym :
  forall p x,
  (Rabs (rounding_floatx rndNE p x - x) = Rabs (rounding_floatx rndNE p (Rabs x) - Rabs x))%R.
Proof.
intros p x.
destruct (Rle_or_lt 0 x) as [H|H].
rewrite (Rabs_right _ (Rle_ge _ _ H)).
exact (refl_equal _).
rewrite (Rabs_left _ H).
rewrite round_NE_opp.
unfold Rminus.
rewrite <- Ropp_plus_distr.
now rewrite Rabs_Ropp.
Qed.

Instance zpos_gt_0 : forall p, Prec_gt_0 (Zpos p).
easy.
Qed.

Lemma float_absolute_n_whole :
  forall c p d k x,
  (Rabs x < bpow radix2 k)%R ->
  (Rabs (rounding_float (Znearest c) p d x - x) <= bpow radix2 (FLT_exp d (Zpos p) k - 1))%R.
Proof with auto with typeclass_instances.
intros c p d k x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, round_0, Rminus_0_r, Rabs_R0...
apply bpow_ge_0.
apply Rle_trans with (/2 * ulp radix2 (FLT_exp d (Zpos p)) x)%R.
apply error_le_half_ulp...
rewrite ulp_neq_0; trivial.
rewrite <- (bpow_plus radix2 (-1)).
apply bpow_le.
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply Zplus_le_compat_l.
unfold cexp.
apply monotone_exp...
now apply mag_le_bpow.
Qed.

Lemma floatx_absolute_n_whole :
  forall c p k x,
  (Rabs x < bpow radix2 k)%R ->
  (Rabs (rounding_floatx (Znearest c) p x - x) <= bpow radix2 (FLX_exp (Zpos p) k - 1))%R.
Proof with auto with typeclass_instances.
intros c p k x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, round_0, Rminus_0_r, Rabs_R0...
apply bpow_ge_0.
apply Rle_trans with (/2 * ulp radix2 (FLX_exp (Zpos p)) x)%R.
apply error_le_half_ulp...
rewrite ulp_neq_0; trivial.
rewrite <- (bpow_plus radix2 (-1)).
apply bpow_le.
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply Zplus_le_compat_l.
unfold cexp.
apply monotone_exp...
now apply mag_le_bpow.
Qed.

Lemma float_absolute_inv_n_whole :
  forall c p d k x,
  (Rabs (rounding_float (Znearest c) p d x) < bpow radix2 k)%R ->
  (Rabs (rounding_float (Znearest c) p d x - x) <= bpow radix2 (FLT_exp d (Zpos p) k - 1))%R.
Proof with auto with typeclass_instances.
intros c p d k x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, round_0, Rminus_0_r, Rabs_R0...
apply bpow_ge_0.
apply Rle_trans with (/2 * ulp radix2 (FLT_exp d (Zpos p)) x)%R.
apply error_le_half_ulp...
rewrite ulp_neq_0; trivial.
rewrite <- (bpow_plus radix2 (-1)).
apply bpow_le.
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply Zplus_le_compat_l.
unfold cexp.
destruct (Zle_or_lt (mag radix2 x) k) as [Hk1|Hk1].
apply monotone_exp...
destruct (Zle_or_lt (mag radix2 x) d) as [Hk2|Hk2].
unfold FLT_exp.
clear -Hk1 Hk2 ; zify ; omega.
elim Rlt_not_le with (1 := Hx) ; clear Hx.
apply Rle_trans with (bpow radix2 (Z.max k d)).
apply bpow_le.
apply Z.le_max_l.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLT_exp.
clear ; zify ; omega.
destruct (mag radix2 x) as (ex,Ex) ; simpl in *.
apply Rle_trans with (2 := proj1 (Ex Hx0)).
apply bpow_le.
clear -Hk1 Hk2 ; zify ; omega.
Qed.

Lemma floatx_absolute_inv_n_whole :
  forall c p k x,
  (Rabs (rounding_floatx (Znearest c) p x) < bpow radix2 k)%R ->
  (Rabs (rounding_floatx (Znearest c) p x - x) <= bpow radix2 (FLX_exp (Zpos p) k - 1))%R.
Proof with auto with typeclass_instances.
intros c p k x Hx.
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, round_0, Rminus_0_r, Rabs_R0...
apply bpow_ge_0.
apply Rle_trans with (/2 * ulp radix2 (FLX_exp (Zpos p)) x)%R.
apply error_le_half_ulp...
rewrite ulp_neq_0; trivial.
rewrite <- (bpow_plus radix2 (-1)).
apply bpow_le.
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply Zplus_le_compat_l.
unfold cexp.
apply monotone_exp...
destruct (Zle_or_lt (mag radix2 x) k) as [Hk1|Hk1].
exact Hk1.
elim Rlt_not_le with (1 := Hx) ; clear Hx.
apply abs_round_ge_generic...
apply generic_format_bpow.
unfold FLX_exp.
clear ; zify ; omega.
destruct (mag radix2 x) as (ex,Ex) ; simpl in *.
apply Rle_trans with (2 := proj1 (Ex Hx0)).
apply bpow_le.
clear -Hk1 ; omega.
Qed.

Lemma Zmax_inf_l :
 forall m n : Z, (n <= m)%Z -> Z.max m n = m.
intros m n H.
generalize (Z.le_ge _ _ H).
unfold Z.max, Z.ge.
case (m ?= n)%Z ; intros ; try exact (refl_equal _).
elim H0.
exact (refl_equal _).
Qed.

Lemma float_relative_n_whole :
  forall c p d x,
  (bpow radix2 (d + Zpos p - 1) <= Rabs x)%R ->
  (Rabs ((rounding_float (Znearest c) p d x - x) / x) <= bpow radix2 (-Zpos p))%R.
Proof.
intros c p d x Hx.
assert (Hx0: x <> 0%R).
intros Hx0.
apply Rle_not_lt with (1 := Hx).
rewrite Hx0, Rabs_R0.
apply bpow_gt_0.
destruct (relative_error_N_FLT_ex radix2 d (Zpos p) (refl_equal _) c x Hx) as (eps, (Hr1, Hr2)).
rewrite Hr2.
replace ((x * (1 + eps) - x) / x)%R with eps by now field.
revert Hr1.
rewrite <- (bpow_plus radix2 (-1)%Z).
now rewrite (Zplus_comm (- Zpos p)), Zplus_assoc.
Qed.

Lemma float_relative_inv_n_whole :
  forall c p d x,
  (bpow radix2 (d + Zpos p - 1) < Rabs (rounding_float (Znearest c) p d x))%R ->
  (Rabs ((rounding_float (Znearest c) p d x - x) / x) <= bpow radix2 (-Zpos p))%R.
Proof with auto with typeclass_instances.
intros c p d x Hx.
apply float_relative_n_whole.
apply Rnot_lt_le.
contradict Hx.
apply Rle_not_lt.
apply abs_round_le_generic...
apply generic_format_bpow.
unfold FLT_exp.
ring_simplify (d + Zpos p - 1 + 1 - Zpos p)%Z.
rewrite Zmax_idempotent.
clear ; zify ; omega.
now apply Rlt_le.
Qed.

Theorem fix_of_float :
  forall rdir x p k1 k2,
  Zle_bool k2 k1 = true ->
  FIX (rounding_float rdir p k1 x) k2.
Proof.
intros rdir x p k1 k2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX.
eexists (Float2 _ _) ; repeat split.
simpl.
unfold cexp.
apply Z.le_trans with (1 := H).
apply Z.le_max_r.
Qed.

Theorem flt_of_float :
  forall rdir {Hrnd : Valid_rnd rdir} x p1 p2 k,
  Zle_bool (Zpos p1) (Zpos p2) = true ->
  FLT (rounding_float rdir p1 k x) p2.
Proof with auto with typeclass_instances.
intros rdir Hrnd x p1 p2 k H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FLT.
destruct (FLT_format_generic radix2 k (Zpos p1) (Generic_fmt.round radix2 (FLT_exp k (Zpos p1)) rdir x))
  as ((m, e), H1, H2, _).
apply generic_format_round...
rewrite H1.
eexists (Float2 _ _) ; repeat split.
apply Z.lt_le_trans with (1 := H2).
change (Zpower_pos 2 p2) with (Zpower radix2 (Zpos p2)).
now apply Zpower_le.
Qed.

Theorem flt_of_floatx :
  forall rdir {Hrnd : Valid_rnd rdir} x p1 p2,
  Zle_bool (Zpos p1) (Zpos p2) = true ->
  FLT (rounding_floatx rdir p1 x) p2.
Proof with auto with typeclass_instances.
intros rdir Hrnd x p1 p2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FLT.
destruct (FLX_format_generic radix2 (Zpos p1) (Generic_fmt.round radix2 (FLX_exp (Zpos p1)) rdir x))
  as ((m, e), H1, H2).
apply generic_format_round...
rewrite H1.
eexists (Float2 _ _) ; repeat split.
apply Z.lt_le_trans with (1 := H2).
change (Zpower_pos 2 p2) with (Zpower radix2 (Zpos p2)).
now apply Zpower_le.
Qed.

Theorem float_of_fix_flt :
  forall rdir {Hrnd : Valid_rnd rdir},
  forall x : R,
  forall d1 d2 : Z, forall p1 p2 : positive,
  FIX x d1 -> FLT x p1 ->
  Zle_bool d2 d1 && Zle_bool (Zpos p1) (Zpos p2) = true ->
  rounding_float rdir p2 d2 x = x.
Proof with auto with typeclass_instances.
intros rdir Hrnd x d1 d2 p1 p2 (f1,(Hx1,Hx2)) (f2,(Hx3,Hx4)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
apply round_generic...
destruct f1 as (m1, e1).
destruct f2 as (m2, e2).
destruct (Z.eq_dec m2 0) as [Hm|Hm].
rewrite <- Hx3.
unfold float2R.
rewrite Hm, F2R_0.
apply generic_format_0.
assert (mag radix2 (F2R (Float radix2 m2 e2)) <= Zpos p2 + e2)%Z.
rewrite mag_F2R with (1 := Hm).
apply Zplus_le_compat_r.
apply Z.le_trans with (2 := H2).
apply bpow_lt_bpow with radix2.
destruct (mag radix2 (IZR m2)) as (n2, Hn).
simpl.
specialize (Hn (IZR_neq _ _ Hm)).
apply Rle_lt_trans with (1 := proj1 Hn).
rewrite <- abs_IZR.
now apply IZR_lt.
destruct (Zle_or_lt e1 e2) as [He|He].
(* *)
rewrite <- Hx3.
apply generic_format_F2R.
intros _ ; simpl.
apply Z.max_lub.
clear -H ; omega.
apply Z.le_trans with (1 := H1).
now apply Z.le_trans with e1.
(* *)
rewrite <- Hx1.
apply generic_format_F2R.
intros _ ; simpl.
apply Z.max_lub.
unfold float2R in Hx1. simpl in Hx1.
rewrite Hx1, <- Hx3.
unfold float2R. simpl.
omega.
now apply Z.le_trans with d1.
Qed.

Theorem floatx_of_flt :
  forall rdir {Hrnd : Valid_rnd rdir},
  forall x : R,
  forall p1 p2 : positive,
  FLT x p1 ->
  Zle_bool (Zpos p1) (Zpos p2) = true ->
  rounding_floatx rdir p2 x = x.
Proof with auto with typeclass_instances.
intros rdir Hrnd x p1 p2 [[m e] [Hx1 Hx2]] Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
apply round_generic...
rewrite <- Hx1.
apply generic_format_F2R.
unfold cexp.
intros Hm ; simpl.
rewrite mag_F2R with (1 := Hm).
simpl.
unfold FLX_exp.
cut (mag radix2 (IZR m) <= Zpos p1)%Z.
clear -H1 ; omega.
apply bpow_lt_bpow with radix2.
destruct (mag radix2 (IZR m)) as [n Hn].
simpl.
specialize (Hn (IZR_neq _ _ Hm)).
apply Rle_lt_trans with (1 := proj1 Hn).
rewrite <- abs_IZR.
now apply IZR_lt.
Qed.

Existing Instance valid_rnd_Gf.

Definition round_helper (rnd : float2 -> float2) (xi zi : FF) :=
 Fle2 (lower zi) (rnd (lower xi)) &&
 Fle2 (rnd (upper xi)) (upper zi).

Theorem float_round :
  forall rdir p d x xi zi,
  BND x xi ->
  round_helper (round (rndG_g rdir) (FLT_exp d (Zpos p))) xi zi = true ->
  BND (rounding_float (rndG_f rdir) p d x) zi.
Proof with auto with typeclass_instances.
intros rdir p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite rndG_conversion. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite rndG_conversion. clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
apply round_le...
apply Hx.
apply Rle_trans with (2 := H2).
apply round_le...
apply Hx.
Qed.

Definition float_round_dn := float_round roundDN_cs.
Definition float_round_up := float_round roundUP_cs.
Definition float_round_zr := float_round roundZR_cs.
Definition float_round_ne := float_round roundNE_cs.
Definition float_round_na := float_round roundNA_cs.

Theorem floatx_round :
  forall rdir p x xi zi,
  BND x xi ->
  round_helper (round (rndG_g rdir) (FLX_exp (Zpos p))) xi zi = true ->
  BND (rounding_floatx (rndG_f rdir) p x) zi.
Proof with auto with typeclass_instances.
intros rdir p x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite rndG_conversion. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite rndG_conversion. clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
apply round_le...
apply Hx.
apply Rle_trans with (2 := H2).
apply round_le...
apply Hx.
Qed.

Definition floatx_round_dn := floatx_round roundDN_cs.
Definition floatx_round_up := floatx_round roundUP_cs.
Definition floatx_round_zr := floatx_round roundZR_cs.
Definition floatx_round_ne := floatx_round roundNE_cs.
Definition floatx_round_na := floatx_round roundNA_cs.

Definition enforce_helper (fexp : Z -> Z) (xi zi : FF) :=
 Fle2 (lower zi) (round roundUP fexp (lower xi)) &&
 Fle2 (round roundDN fexp (upper xi)) (upper zi).

Theorem float_enforce :
  forall rdir {Hrnd : Valid_rnd rdir} p d x xi zi,
  BND (rounding_float rdir p d x) xi ->
  enforce_helper (FLT_exp d (Zpos p)) xi zi = true ->
  BND (rounding_float rdir p d x) zi.
Proof with auto with typeclass_instances.
intros rdir Hrnd p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite (rndG_conversion roundUP_cs). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite (rndG_conversion roundDN_cs). clear H2. intro H2.
revert Hx.
intros (Hx1, Hx2).
split.
apply Rle_trans with (1 := H1).
rewrite <- (round_generic _ _ rndUP _ (generic_format_round radix2 (FLT_exp d (Zpos p)) rdir x)).
apply round_le...
apply Rle_trans with (2 := H2).
rewrite <- (round_generic _ _ rndDN _ (generic_format_round radix2 (FLT_exp d (Zpos p)) rdir x)).
apply round_le...
Qed.

Theorem floatx_enforce :
  forall rdir {Hrnd : Valid_rnd rdir} p x xi zi,
  BND (rounding_floatx rdir p x) xi ->
  enforce_helper (FLX_exp (Zpos p)) xi zi = true ->
  BND (rounding_floatx rdir p x) zi.
Proof with auto with typeclass_instances.
intros rdir Hrnd p x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite (rndG_conversion roundUP_cs). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite (rndG_conversion roundDN_cs). clear H2. intro H2.
revert Hx.
intros (Hx1, Hx2).
split.
apply Rle_trans with (1 := H1).
rewrite <- (round_generic _ _ rndUP _ (generic_format_round radix2 (FLX_exp (Zpos p)) rdir x)).
apply round_le...
apply Rle_trans with (2 := H2).
rewrite <- (round_generic _ _ rndDN _ (generic_format_round radix2 (FLX_exp (Zpos p)) rdir x)).
apply round_le...
Qed.

Definition float_absolute_n_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 1)%Z in
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_n :
  forall c p d x xi zi,
  ABS x xi ->
  float_absolute_n_helper p d xi zi = true ->
  BND (rounding_float (Znearest c) p d x - x) zi.
Proof with auto with typeclass_instances.
intros c p d x xi zi Hx Hb.
assert (H: (Rabs (rounding_float (Znearest c) p d x - x) <= bpow radix2 (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 1))%R).
(* *)
destruct (Req_dec x 0) as [Hx0|Hx0].
rewrite Hx0, round_0, Rminus_0_r, Rabs_R0...
apply bpow_ge_0.
replace (bpow radix2 (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 1)) with (/2 * ulp radix2 (FLT_exp d (Zpos p)) (upper xi))%R.
(* . *)
apply Rle_trans with (/2 * ulp radix2 (FLT_exp d (Zpos p)) x)%R.
apply error_le_half_ulp...
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
now apply IZR_lt.
rewrite <- ulp_abs.
apply ulp_le_pos...
apply Rabs_pos.
apply Hx.
(* . *)
assert (Hm0: (Fnum (upper xi)) <> Z0).
assert (Hx1 := Rabs_no_R0 _ Hx0).
contradict Hx1.
apply Rle_antisym.
replace 0%R with (float2R (upper xi)).
apply Hx.
clear -Hx1.
destruct (upper xi).
simpl in Hx1.
rewrite Hx1.
apply float2_zero.
apply Rabs_pos.
rewrite ulp_neq_0.
2: now apply F2R_neq_0.
rewrite <- (bpow_plus radix2 (-1)).
unfold Zminus.
rewrite (Zplus_comm _ (-1)).
apply (f_equal (fun e => bpow radix2 (-1 + e))).
clear -Hm0.
destruct (upper xi) as (m, e).
unfold cexp, float2R.
rewrite mag_F2R with (1 := Hm0).
rewrite <- Zdigits_mag with (1 := Hm0).
simpl.
rewrite <- Zdigits_abs.
rewrite Zplus_comm.
destruct m as [|m|m] ; unfold Z.abs.
now elim Hm0.
now rewrite <- digits2_digits.
now rewrite <- digits2_digits.
(* *)
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
unfold float2R.
rewrite (F2R_Zopp _ 1%Z).
rewrite F2R_bpow.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply (Rle_trans _ _ _ (Rabs_idem _)).
now rewrite Rabs_Ropp.
apply Rle_trans with (2 := H2).
unfold float2R.
rewrite F2R_bpow.
now apply (Rle_trans _ _ _ (Rabs_idem _)).
Qed.

Definition float_absolute_ne := float_absolute_n (fun x => negb (Z.even x)).
Definition float_absolute_na := float_absolute_n (Zle_bool 0).

Theorem float_absolute_inv_n :
  forall c p d x xi zi,
  ABS (rounding_float (Znearest c) p d x) xi ->
  float_absolute_n_helper p d xi zi = true ->
  BND (rounding_float (Znearest c) p d x - x) zi.
Proof with auto with typeclass_instances.
intros c p d x xi zi Hx Hb.
assert (H: (Rabs (rounding_float (Znearest c) p d x - x) <= bpow radix2 (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 1))%R).
(* *)
replace (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi))) with
  (FLT_exp d (Zpos p) (if Z.eq_dec (Fnum (upper xi)) Z0 then d else (Fexp (upper xi) + Zpos (digits (pos_of_Z (Z.abs (Fnum (upper xi))))))%Z)).
apply float_absolute_inv_n_whole.
apply Rle_lt_trans with (1 := proj2 (proj2 Hx)).
unfold float2R.
case Z.eq_dec ; intros Zx.
rewrite Zx, F2R_0.
apply bpow_gt_0.
rewrite digits2_digits.
rewrite Zpos_pos_of_Z.
rewrite Zdigits_abs, Zplus_comm.
rewrite <- mag_F2R_Zdigits with (1 := Zx).
destruct mag as (ex,Ex) ; simpl.
apply Rle_lt_trans with (1 := RRle_abs _).
apply Ex.
contradict Zx.
apply eq_0_F2R with (1 := Zx).
clear -Zx ; zify ; omega.
unfold float_ulp.
case Z.eq_dec ; intros Zx.
rewrite Zx.
unfold FLT_exp.
clear ; zify ; omega.
revert Zx.
case Fnum ; simpl ; [|easy|easy].
intros H.
now elim H.
(* *)
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
unfold float2R.
rewrite (F2R_Zopp _ 1%Z).
rewrite F2R_bpow.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply (Rle_trans _ _ _ (Rabs_idem _)).
now rewrite Rabs_Ropp.
apply Rle_trans with (2 := H2).
unfold float2R.
rewrite F2R_bpow.
now apply (Rle_trans _ _ _ (Rabs_idem _)).
Qed.

Definition float_absolute_inv_ne := float_absolute_inv_n (fun x => negb (Z.even x)).
Definition float_absolute_inv_na := float_absolute_inv_n (Zle_bool 0).

Definition float_absolute_wide_ne_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 2)%Z in
 Zle_bool d (Fexp u - Zpos p) &&
 Fle2 u (Float2 (Zpos (xI (shift_pos p xH))) e) &&
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_wide_ne :
  forall p d x xi zi,
  ABS x xi ->
  float_absolute_wide_ne_helper p d xi zi = true ->
  BND (rounding_float rndNE p d x - x) zi.
Proof with auto with typeclass_instances.
intros p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). unfold float2R. simpl. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). unfold float2R. simpl. rewrite (F2R_Zopp _ 1%Z), F2R_bpow. clear H3. intro H3.
generalize (Fle2_correct _ _ H4). unfold float2R. simpl. rewrite F2R_bpow. clear H4. intro H4.
set (e := (float_ulp p d (Fnum (upper xi)) (Fexp (upper xi)) - 2)%Z) in H2, H3, H4.
cut (Rabs (rounding_float rndNE p d x - x) <= bpow radix2 e)%R.
(* *)
split.
apply Rle_trans with (1 := H3).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (2 := H).
rewrite <- Rabs_Ropp.
apply Rabs_idem.
apply Rle_trans with (2 := H4).
apply Rle_trans with (2 := H).
apply Rabs_idem.
(* *)
destruct Hx as (_,(_,Hx)).
clear H3 H4 zi.
induction (upper xi).
induction Fnum ; simpl.
cutrewrite (x = R0).
rewrite round_0...
rewrite Rminus_0_r.
rewrite Rabs_R0.
apply bpow_ge_0.
elim (Req_dec x 0) ; intro H.
exact H.
elim Rlt_not_le with (2 := Hx).
rewrite float2_zero.
now apply Rabs_pos_lt.
(* *)
simpl in e, H1.
assert (H9: (e = Fexp + Zpos (digits p0) - Zpos p - 2)%Z).
unfold e, FLT_exp.
rewrite Zmax_inf_l.
exact (refl_equal _).
generalize (Zgt_pos_0 (digits p0)).
omega.
destruct (Rle_or_lt (bpow radix2 (Fexp + Zpos (digits p0) - 1)) (Rabs x)).
(* . *)
rewrite float_absolute_ne_sym.
cutrewrite (rounding_float rndNE p d (Rabs x) = bpow radix2 (Fexp + Zpos (digits p0) - 1) :>R).
rewrite Rabs_left1.
rewrite Ropp_minus_distr.
apply Rle_trans with (F2R (Float radix2 (Zpos (xI (shift_pos p 1))) e) - bpow radix2 (Fexp + Zpos (digits p0) - 1))%R.
unfold Rminus.
apply Rplus_le_compat_r.
exact (Rle_trans _ _ _ Hx H2).
rewrite H9.
rewrite <- F2R_bpow.
change (Float2 (Zpos (shift_pos p 1)~1) (Fexp + Zpos (digits p0) - Zpos p - 2) - Float2 1 (Fexp + Zpos (digits p0) - 1) <=
  bpow radix2 (Fexp + Zpos (digits p0) - Zpos p - 2))%R.
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
simpl.
clear H H9 H2 e H1 Hx xi x d.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p - 2 - (Fexp + Zpos (digits p0) - 1) = Zneg (p + 1))%Z.
cutrewrite (Zpos (xI (shift_pos p 1)) - Zpos (shift_pos (p + 1) 1) = 1)%Z.
unfold float2R.
rewrite F2R_bpow.
apply Rle_refl.
unfold shift_pos.
repeat rewrite iter_nat_of_P.
rewrite <- Pplus_one_succ_r.
rewrite nat_of_P_succ_morphism.
simpl.
now rewrite Z.pos_sub_diag.
rewrite <- Zneg_plus_distr.
rewrite <- (Zopp_neg p).
ring.
apply Rplus_le_reg_r with (Rabs x).
unfold Rminus.
now rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
apply Rle_antisym.
cutrewrite (bpow radix2 (Fexp + Zpos (digits p0) - 1) =
  Generic_fmt.round radix2 (FLT_exp d (Zpos p)) rndNE (F2R (Float radix2 (Zpos (xI (shift_pos p 1))) e)) :>R).
(* .. *)
apply round_le...
exact (Rle_trans _ _ _ Hx H2).
change (F2R (Float radix2 (Zpos (shift_pos p 1)~1) e)) with (float2R (Float2 (Zpos (shift_pos p 1)~1) e)).
rewrite <- (rndG_conversion roundNE_cs).
unfold round, round_pos.
simpl.
cutrewrite (FLT_exp d (Zpos p) (e + Zpos (Pos.succ (digits (shift_pos p 1)))) = e + 2)%Z.
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
now rewrite <- F2R_bpow.
rewrite <- F2R_bpow.
change (F2R (Float radix2 1 (Fexp + Zpos (digits p0) - 1))) with (float2R (Float2 1 (Fexp + Zpos (digits p0) - 1))).
rewrite <- (float2_shl_correct 1 (Fexp + Zpos (digits p0) - 1)%Z (Pos.pred p)).
simpl.
unfold shift_pos.
rewrite iter_nat_of_P.
rewrite <- H4 in H3.
rewrite nat_of_P_succ_morphism in H3.
injection H3.
intro H5.
rewrite H5.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p = Fexp + Zpos (digits p0) - 1 - Zpos (Pos.pred p))%Z.
exact (refl_equal _).
pattern p at 1 ; rewrite <- H4.
rewrite Zpos_succ_morphism.
unfold Z.succ.
ring.
rewrite H9.
cutrewrite (digits (shift_pos p 1) = Pos.succ p)%Z.
repeat rewrite Zpos_succ_morphism.
unfold Z.succ.
cutrewrite (Fexp + Zpos (digits p0) - Zpos p - 2 + (Zpos p + 1 + 1) = Fexp + Zpos (digits p0))%Z. 2: ring.
unfold FLT_exp.
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
(* .. *)
rewrite <- (round_generic radix2 (FLT_exp d (Zpos p)) rndNE (bpow radix2 (Fexp + Zpos (digits p0) - 1))).
apply round_le...
(* . *)
apply generic_format_bpow.
unfold FLT_exp.
rewrite Zmax_inf_l.
generalize (Zgt_pos_0 p).
omega.
generalize (Zgt_pos_0 (digits p0)).
omega.
cutrewrite (e = FLT_exp d (Zpos p) (Fexp + Zpos (digits p0) - 1) - 1)%Z.
now apply float_absolute_n_whole.
unfold e, FLT_exp.
assert (H3 := Zgt_pos_0 (digits p0)).
assert (H4 := Zgt_pos_0 p).
repeat rewrite Zmax_inf_l ; omega.
elim Rlt_not_le with (2 := Hx).
apply Rlt_le_trans with (Float2 0 Fexp).
now apply F2R_lt.
unfold float2R.
rewrite F2R_0.
apply Rabs_pos.
Qed.

Definition float_relative_n_helper (p : positive) (d : Z) (xi zi : FF) :=
 Fle2 (Float2 1 (d + Zpos p - 1)) (lower xi) &&
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem float_relative_n :
  forall c p d x xi zi,
  ABS x xi ->
  float_relative_n_helper p d xi zi = true ->
  REL (rounding_float (Znearest c) p d x) x zi.
Proof.
intros c p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). unfold float2R. simpl. rewrite F2R_bpow. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). unfold float2R. simpl. rewrite (F2R_Zopp _ 1%Z), F2R_bpow. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). unfold float2R. simpl. rewrite F2R_bpow. clear H3. intro H3.
exists ((rounding_float (Znearest c) p d x - x) / x)%R.
split.
assert (Rabs ((rounding_float (Znearest c) p d x - x) / x) <= bpow radix2 (- Zpos p))%R.
apply float_relative_n_whole.
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

Definition float_relative_ne := float_relative_n (fun x => negb (Z.even x)).
Definition float_relative_na := float_relative_n (Zle_bool 0).

Definition floatx_relative_n_helper (p : positive) (zi : FF) :=
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem floatx_relative_n :
  forall c p x zi,
  floatx_relative_n_helper p zi = true ->
  REL (rounding_floatx (Znearest c) p x) x zi.
Proof.
intros c p x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). unfold float2R. simpl. rewrite (F2R_Zopp _ 1%Z), F2R_bpow. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). unfold float2R. simpl. rewrite F2R_bpow. clear H2. intro H2.
destruct (relative_error_N_FLX_ex radix2 (Zpos p) (refl_equal _) c x) as (eps, (Hr1, Hr2)).
exists eps.
refine (conj _ Hr2).
rewrite <- (bpow_plus radix2 (-1)%Z) in Hr1.
rewrite (Zplus_comm (- Zpos p)), Zplus_assoc in Hr1.
split.
apply Rle_trans with (1 := H1).
apply Ropp_le_cancel.
rewrite Ropp_involutive.
apply Rle_trans with (2 := Hr1).
rewrite <- Rabs_Ropp.
apply Rabs_idem.
apply Rle_trans with (2 := H2).
apply Rle_trans with (2 := Hr1).
apply Rabs_idem.
Qed.

Definition floatx_relative_ne := floatx_relative_n (fun x => negb (Z.even x)).
Definition floatx_relative_na := floatx_relative_n (Zle_bool 0).

Definition float_relative_inv_n_helper (p : positive) (d : Z) (xi zi : FF) :=
 Flt2 (Float2 1 (d + Zpos p - 1)) (lower xi) &&
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem float_relative_inv_n :
  forall c p d x xi zi,
  ABS (rounding_float (Znearest c) p d x) xi ->
  float_relative_inv_n_helper p d xi zi = true ->
  REL (rounding_float (Znearest c) p d x) x zi.
Proof with auto with typeclass_instances.
intros c p d x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_correct _ _ H1). unfold float2R. simpl. rewrite F2R_bpow. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). unfold float2R. simpl. rewrite (F2R_Zopp _ 1%Z), F2R_bpow. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). unfold float2R. simpl. rewrite F2R_bpow. clear H3. intro H3.
exists ((rounding_float (Znearest c) p d x - x) / x)%R.
split.
assert (Rabs ((rounding_float (Znearest c) p d x - x) / x) <= bpow radix2 (- Zpos p))%R.
apply float_relative_inv_n_whole.
apply Rlt_le_trans with (1 := H1).
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
apply Rlt_not_le with (1 := H1).
apply Rle_trans with (1 := proj1 (proj2 Hx)).
rewrite H, round_0, Rabs_R0...
apply bpow_ge_0.
Qed.

Definition float_relative_inv_ne := float_relative_inv_n (fun x => negb (Z.even x)).
Definition float_relative_inv_na := float_relative_inv_n (Zle_bool 0).

Definition rel_of_fix_float_n_helper (p : positive) (d xn : Z) (zi : FF) :=
 Zle_bool d xn &&
 Fle2 (lower zi) (Float2 (-1) (Zneg p)) &&
 Fle2 (Float2 1 (Zneg p)) (upper zi).

Theorem rel_of_fix_float_n :
  forall c p d xn x zi,
  FIX x xn ->
  rel_of_fix_float_n_helper p d xn zi = true ->
  REL (rounding_float (Znearest c) p d x) x zi.
Proof with auto with typeclass_instances.
intros c p d xn x zi ((mx, ex), (Hx1, Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). unfold float2R. simpl. rewrite (F2R_Zopp _ 1%Z), F2R_bpow. clear H2. intro H2.
generalize (Fle2_correct _ _ H3). unfold float2R. simpl. rewrite F2R_bpow. clear H3. intro H3.
destruct (Rle_or_lt (Rabs x) (bpow radix2 (d + Zpos p))) as [He|He].
(* *)
rewrite round_generic...
exists 0%R.
repeat split.
apply Rle_trans with (1 := H2).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply bpow_ge_0.
apply Rle_trans with (2 := H3).
apply bpow_ge_0.
now rewrite Rplus_0_r, Rmult_1_r.
apply generic_format_FLT_FIX...
rewrite <- Hx1.
apply generic_format_F2R.
intros _.
now apply Z.le_trans with xn.
(* *)
exists ((rounding_float (Znearest c) p d x - x) / x)%R.
assert (Rabs ((rounding_float (Znearest c) p d x - x) / x) <= bpow radix2 (- Zpos p))%R.
apply float_relative_n_whole.
apply Rlt_le.
apply Rlt_trans with (2 := He).
apply bpow_lt.
pattern (d + Zpos p)%Z at 2 ; rewrite <- Zplus_0_r.
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

Definition rel_of_fix_float_ne := rel_of_fix_float_n (fun x => negb (Z.even x)).
Definition rel_of_fix_float_na := rel_of_fix_float_n (Zle_bool 0).

Theorem fix_float_of_fix :
  forall rdir {Hrnd : Valid_rnd rdir} p d xn zn x,
  FIX x xn ->
  Zle_bool zn xn = true ->
  FIX (rounding_float rdir p d x) zn.
Proof with auto with typeclass_instances.
intros rdir Hrnd p d xn zn x Hx Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
apply FIX_iff_generic.
apply generic_round_generic...
apply FIX_iff_generic.
now apply fix_le with xn.
Qed.

Theorem fix_floatx_of_fix :
  forall rdir {Hrnd : Valid_rnd rdir} p xn zn x,
  FIX x xn ->
  Zle_bool zn xn = true ->
  FIX (rounding_floatx rdir p x) zn.
Proof with auto with typeclass_instances.
intros rdir Hrnd p xn zn x Hx Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
apply FIX_iff_generic.
apply generic_round_generic...
apply FIX_iff_generic.
now apply fix_le with xn.
Qed.

Theorem flt_float_of_flt :
  forall rdir {Hrnd : Valid_rnd rdir} p d xn zn x,
  FLT x xn ->
  Zle_bool (Zpos xn) (Zpos zn) = true ->
  FLT (rounding_float rdir p d x) zn.
Proof with auto with typeclass_instances.
intros rdir Hrnd p d xn zn x H Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
apply FLT_iff_generic.
apply generic_round_generic...
apply FLT_iff_generic.
now apply flt_le with xn.
Qed.

Theorem flt_floatx_of_flt :
  forall rdir {Hrnd : Valid_rnd rdir} p xn zn x,
  FLT x xn ->
  Zle_bool (Zpos xn) (Zpos zn) = true ->
  FLT (rounding_floatx rdir p x) zn.
Proof with auto with typeclass_instances.
intros rdir Hrnd p xn zn x H Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
apply FLT_iff_generic.
apply generic_round_generic...
apply FLT_iff_generic.
now apply flt_le with xn.
Qed.
