Require Import Classical.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_pred_bnd.
Require Import Gappa_round_def.
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

Definition fixed_ext (rdir : round_dir) (e : Z) :=
 round_extension rdir (fixed_shift e) (good_shift e).

Definition rounding_fixed (rdir : round_dir) (e : Z) :=
 projT1 (fixed_ext rdir e).

Axiom log2:
 forall x : R, (0 < x)%R ->
 exists k : Z, (powerRZ 2 (k - 1) <= x < powerRZ 2 k)%R.

Theorem fix_of_fixed :
 forall rdir : round_dir,
 forall x : R, forall e1 e2 : Z,
 Zle_bool e2 e1 = true ->
 FIX (rounding_fixed rdir e1 x) e2.
intros rdir x e1 e2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX.
unfold rounding_fixed.
generalize (fixed_ext rdir e1).
intros (fext,(H1,(H2,(H3,H4)))).
simpl.
case (Req_dec (fext x) R0) ; intro H0.
exists (Float2 Z0 e1).
split. 2: exact H.
rewrite H0.
unfold float2R.
apply Rmult_0_l.
case (Req_dec x R0).
intro H5.
elim H0.
replace x with (float2R (Float2 Z0 e1)).
rewrite (H2 (Float2 Z0 e1)).
unfold round.
simpl.
unfold float2R.
apply Rmult_0_l.
rewrite H5.
unfold float2R.
apply Rmult_0_l.
intro H5.
assert (0 < Rabs x)%R.
apply Rabs_pos_lt with (1 := H5).
generalize (log2 (Rabs x) H6).
intros (k,H7).
generalize (H3 x k H7).
intros (f,(H8,H9)).
exists f.
split.
apply sym_eq with (1 := H8).
rewrite H9.
exact H.
Qed.

Theorem fixed_of_fix :
 forall rdir : round_dir,
 forall x : R, forall e1 e2 : Z, forall xi : FF,
 FIX x e1 ->
 Zle_bool e2 e1 && contains_zero_helper xi = true ->
 BND (rounding_fixed rdir e2 x - x) xi.
intros rdir x e1 e2 xi (f,(Hx1,Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
cutrewrite (rounding_fixed rdir e2 x = x).
unfold Rminus.
rewrite (Rplus_opp_r x).
apply contains_zero with (1 := H2).
rewrite <- Hx1.
unfold rounding_fixed.
generalize (fixed_ext rdir e2).
intros (fext,(H3,(H4,H5))).
simpl.
rewrite (H4 f).
generalize (Zle_trans _ _ _ H1 Hx2).
clear Hx1 x H2 xi H3 H4 H5 fext Hx2 H1 e1.
induction f.
induction Fnum ; intro.
unfold round, float2R.
simpl.
ring.
unfold round.
simpl.
rewrite round_rexp_exact.
apply refl_equal.
exact H.
unfold round.
simpl.
rewrite round_rexp_exact.
apply refl_equal.
exact H.
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
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
unfold rounding_fixed.
generalize (fixed_ext rdir e).
intros (fext,(H3,(H4,H5))).
simpl.
split.
apply Rle_trans with (1 := H1).
rewrite <- H4.
apply H3.
apply Rle_trans with (2 := H2).
rewrite <- H4.
apply H3.
Qed.

Definition fixed_error_dn_helper (e : Z) (zi : FF) :=
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fpos0 (upper zi).

Theorem fixed_error_dn :
 forall e : Z, forall x : R, forall zi : FF,
 fixed_error_dn_helper e zi = true ->
 BND (rounding_fixed roundDN e x - x) zi.
intros e x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
unfold rounding_fixed.
generalize (fixed_ext roundDN e).
intros (fext,(H3,(H4,(H5,H6)))).
simpl.
cut (fext x <= x < fext x + (Float2 1 e))%R.
intro H.
split.
apply Rle_trans with (1 := H1).
unfold float2R.
simpl.
rewrite Ropp_mult_distr_l_reverse.
replace (1 * powerRZ 2 e)%R with (float2R (Float2 1 e)). 2: apply refl_equal.
apply Rplus_le_reg_l with (x + Float2 1 e)%R.
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
cutrewrite (x + Float2 1 e + (fext x - x) = fext x + Float2 1 e)%R.
2: ring.
apply Rlt_le with (1 := proj2 H).
apply Rle_trans with (2 := H2).
rewrite <- (Rplus_opp_r x).
unfold Rminus.
apply Rplus_le_compat_r.
exact (proj1 H).
case (Req_dec x R0) ; intro H0.
rewrite H0.
cutrewrite (fext 0 = 0)%R.
split. apply Rle_refl.
unfold float2R. simpl.
rewrite Rplus_0_l.
rewrite Rmult_1_l.
auto with real.
cutrewrite (fext R0 = fext (Float2 0 0)).
rewrite H4.
apply round_zero.
apply (f_equal fext).
unfold float2R. simpl.
auto with real.
assert (0 < Rabs x)%R.
apply Rabs_pos_lt with (1 := H0).
generalize (log2 (Rabs x) H).
intros (k,H7).
generalize (H5 x k H7).
intros (f,(H8,H9)).
rewrite H8.
replace f with (Float2 (Fnum f) (Fexp f)). 2: induction f ; apply refl_equal.
rewrite H9.
unfold fixed_shift.
cutrewrite (Float2 (Fnum f) e + Float2 1 e = Float2 (Fnum f + 1) e)%R.
generalize (H6 x).
intros (f1, (f2, (H10, H11))).
split.
apply Rle_trans with (2 := proj1 H10).
Admitted.

End Gappa_fixed.
