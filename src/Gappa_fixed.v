Require Import Bool.
Require Import ZArith.
Require Import Reals.
Require Import Fcore.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_pred_bnd.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.
Require Import Gappa_round.

Section Gappa_fixed.

Definition fixed_shift (e : Z) (_ : Z) := e.

Lemma good_shift :
 forall e : Z,
 good_rexp (fixed_shift e).
unfold fixed_shift. split.
omega.
split.
apply Zle_refl.
intros l _. clear l.
apply refl_equal.
Qed.

Definition rounding_fixed (rdir : round_dir) (e : Z) :=
 round_extension rdir (fixed_shift e) (good_shift e).

Theorem fix_of_fixed :
  forall rdir : round_dir,
  forall x : R, forall k1 k2 : Z,
  Zle_bool k2 k1 = true ->
  FIX (rounding_fixed rdir k1 x) k2.
Proof.
intros rdir x k1 k2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX, rounding_fixed.
rewrite round_extension_conversion.
unfold rounding.
rewrite <- float2_float.
eexists ; repeat split.
exact H.
Qed.

Theorem fixed_of_fix :
  forall rdir x e1 e2 xi,
  FIX x e1 ->
  Zle_bool e2 e1 && contains_zero_helper xi = true ->
  BND (rounding_fixed rdir e2 x - x) xi.
Proof.
intros rdir x e1 e2 xi ((m,e),(Hx1,Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
unfold rounding_fixed.
rewrite round_extension_conversion.
rewrite rounding_generic.
now apply sub_refl.
rewrite <- Hx1.
rewrite float2_float.
apply generic_format_canonic_exponent.
now apply Zle_trans with e1.
Qed.

Definition bnd_of_bnd_fix_helper (xi zi : FF) (e : Z) :=
 Fle2 (lower zi) (round roundUP (fixed_shift e) (lower xi)) &&
 Fle2 (round roundDN (fixed_shift e) (upper xi)) (upper zi).

Theorem bnd_of_bnd_fix :
  forall x xn xi zi,
  BND x xi -> FIX x xn ->
  bnd_of_bnd_fix_helper xi zi xn = true ->
  BND x zi.
Proof.
intros x xn xi zi Hxb ((m,e),(Hx1,Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite rndG_conversion. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite rndG_conversion. clear H2. intro H2.
rewrite float2_float in Hx1.
rewrite <- Hx1.
rewrite <- Hx1 in Hxb.
split.
apply Rle_trans with (1 := H1).
rewrite <- (rounding_generic radix2 (fixed_shift xn) (ZrndG roundUP) (F2R (Float radix2 m e))).
apply rounding_monotone.
apply FIX_exp_correct.
apply Hxb.
now apply generic_format_canonic_exponent.
apply Rle_trans with (2 := H2).
rewrite <- (rounding_generic radix2 (fixed_shift xn) (ZrndG roundDN) (F2R (Float radix2 m e))).
apply rounding_monotone.
apply FIX_exp_correct.
apply Hxb.
now apply generic_format_canonic_exponent.
Qed.

Definition round_helper (rnd : float2 -> float2) (xi zi : FF) :=
 Fle2 (lower zi) (rnd (lower xi)) &&
 Fle2 (rnd (upper xi)) (upper zi).

Theorem fixed_round :
 forall rdir : round_dir, forall e : Z,
 forall x : R, forall xi zi : FF,
 BND x xi ->
 round_helper (round rdir (fixed_shift e)) xi zi = true ->
 BND (rounding_fixed rdir e x) zi.
intros rdir e x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite <- (round_extension_float2 rdir _ (good_shift e)). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite <- (round_extension_float2 rdir _ (good_shift e)). clear H2. intro H2.
unfold rounding_fixed.
split.
apply Rle_trans with (1 := H1).
apply round_extension_monotone.
exact (proj1 Hx).
apply Rle_trans with (2 := H2).
apply round_extension_monotone.
exact (proj2 Hx).
Qed.

Definition fixed_error_dn_helper (e : Z) (zi : FF) :=
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fpos0 (upper zi).

Theorem fixed_error_dn :
  forall e x zi,
  fixed_error_dn_helper e zi = true ->
  BND (rounding_fixed roundDN e x - x) zi.
Proof.
intros e x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
unfold rounding_fixed.
rewrite round_extension_conversion.
split.
(* *)
apply Rle_trans with (1 := H1).
destruct (Rabs_def2 _ _ (ulp_error radix2 _ (good_shift e) (ZrndG roundDN) x)) as (_, H).
apply Rlt_le.
rewrite float2_float.
rewrite <- (opp_F2R _ 1%Z).
now rewrite F2R_bpow.
(* *)
apply Rle_trans with (2 := H2).
apply Rle_minus.
rewrite (rounding_ext _ _ _ ZrndDN) with (1 := roundDN_DN).
eapply generic_DN_pt.
apply good_shift.
Qed.

End Gappa_fixed.
