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

Global Notation rounding_fixed rdir e :=
  (Fcore_generic_fmt.round radix2 (FIX_exp e) rdir) (only parsing).

Section Gappa_fixed.

Theorem fix_of_fixed :
  forall rdir,
  forall x : R, forall k1 k2 : Z,
  Zle_bool k2 k1 = true ->
  FIX (rounding_fixed rdir k1 x) k2.
Proof.
intros rdir x k1 k2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX.
eexists (Float2 _ _) ; repeat split.
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
rewrite round_generic.
now apply sub_refl.
rewrite <- Hx1.
apply generic_format_canonic_exponent.
now apply Zle_trans with e1.
Qed.

Definition bnd_of_bnd_fix_helper (xi zi : FF) (e : Z) :=
  Fle2 (lower zi) (round roundUP (FIX_exp e) (lower xi)) &&
  Fle2 (round roundDN (FIX_exp e) (upper xi)) (upper zi).

Theorem bnd_of_bnd_fix :
  forall x xn xi zi,
  BND x xi -> FIX x xn ->
  bnd_of_bnd_fix_helper xi zi xn = true ->
  BND x zi.
Proof.
intros x xn xi zi Hxb ((m,e),(Hx1,Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite (rndG_conversion roundUP_cs). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite (rndG_conversion roundDN_cs). clear H2. intro H2.
rewrite <- Hx1.
rewrite <- Hx1 in Hxb.
split.
apply Rle_trans with (1 := H1).
unfold float2R at 2. simpl.
rewrite <- (round_generic radix2 (FIX_exp xn) rndUP (F2R (Float radix2 m e))).
apply round_monotone.
apply FIX_exp_correct.
apply Hxb.
now apply generic_format_canonic_exponent.
apply Rle_trans with (2 := H2).
unfold float2R at 1. simpl.
rewrite <- (round_generic radix2 (FIX_exp xn) rndDN (F2R (Float radix2 m e))).
apply round_monotone.
apply FIX_exp_correct.
apply Hxb.
now apply generic_format_canonic_exponent.
Qed.

Definition round_helper (rnd : float2 -> float2) (xi zi : FF) :=
 Fle2 (lower zi) (rnd (lower xi)) &&
 Fle2 (rnd (upper xi)) (upper zi).

Theorem fixed_round :
  forall rdir e x xi zi,
  BND x xi ->
  round_helper (round (rndG_g rdir) (FIX_exp e)) xi zi = true ->
  BND (rounding_fixed (rndG_f rdir) e x) zi.
Proof.
intros rdir e x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite rndG_conversion. clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite rndG_conversion. clear H2. intro H2.
split.
apply Rle_trans with (1 := H1).
apply round_monotone.
apply FIX_exp_correct.
apply Hx.
apply Rle_trans with (2 := H2).
apply round_monotone.
apply FIX_exp_correct.
apply Hx.
Qed.

Definition fixed_round_dn := fixed_round roundDN_cs.
Definition fixed_round_up := fixed_round roundUP_cs.
Definition fixed_round_zr := fixed_round roundZR_cs.
Definition fixed_round_ne := fixed_round roundNE_cs.

Definition fixed_error_dn_helper (e : Z) (zi : FF) :=
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fpos0 (upper zi).

Theorem fixed_error_dn :
  forall e x zi,
  fixed_error_dn_helper e zi = true ->
  BND (rounding_fixed rndDN e x - x) zi.
Proof.
intros e x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
split.
(* *)
apply Rle_trans with (1 := H1).
destruct (Rabs_def2 _ _ (ulp_error radix2 _ (FIX_exp_correct e) rndDN x)) as (_, H).
apply Rlt_le.
unfold float2R.
rewrite <- (opp_F2R _ 1%Z).
now rewrite F2R_bpow.
(* *)
apply Rle_trans with (2 := H2).
apply Rle_minus.
eapply round_DN_pt.
apply FIX_exp_correct.
Qed.

End Gappa_fixed.
