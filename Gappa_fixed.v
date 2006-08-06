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

Definition rounding_fixed (rdir : round_dir) (e : Z) :=
 round_extension rdir (fixed_shift e) (good_shift e).

Theorem fix_of_fixed :
 forall rdir : round_dir,
 forall x : R, forall k1 k2 : Z,
 Zle_bool k2 k1 = true ->
 FIX (rounding_fixed rdir k1 x) k2.
intros rdir x k1 k2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX, rounding_fixed.
generalize (total_order_T 0 x).
intros [[Hx|Hx]|Hx].
generalize (round_extension_prop_pos rdir (fixed_shift k1) (good_shift k1) _ Hx).
intros (m1,(m2,(e1,(e2,(H1,(H2,(_,(H3,_)))))))).
rewrite H2.
unfold round. simpl.
exists (match round_pos (rpos rdir) (fixed_shift k1) m1 e1 with (n,e) =>
  match n with N0 => Float2 0 k1 | Npos p => Float2 (Zpos p) e end end).
split.
case (round_pos (rpos rdir) (fixed_shift k1) m1 e1) ; intros.
case n ; intros.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
induction (round_pos (rpos rdir) (fixed_shift k1) m1 e1).
unfold fixed_shift in H3. simpl in H3.
rewrite <- H3.
case a ; intros ; exact H.
exists (Float2 0 k1).
split.
rewrite <- Hx.
rewrite round_extension_zero.
unfold float2R. apply Rmult_0_l.
exact H.
generalize (round_extension_prop_neg rdir (fixed_shift k1) (good_shift k1) _ Hx).
intros (m1,(m2,(e1,(e2,(H1,(H2,(_,(H3,_)))))))).
rewrite H2.
unfold round. simpl.
exists (match round_pos (rneg rdir) (fixed_shift k1) m1 e1 with (n,e) =>
  match n with N0 => Float2 0 k1 | Npos p => Float2 (Zneg p) e end end).
split.
case (round_pos (rneg rdir) (fixed_shift k1) m1 e1) ; intros.
case n ; intros.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
induction (round_pos (rneg rdir) (fixed_shift k1) m1 e1).
unfold fixed_shift in H3. simpl in H3.
rewrite <- H3.
case a ; intros ; exact H.
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
cutrewrite (rounding_fixed rdir e2 x = x :>R).
unfold Rminus.
rewrite (Rplus_opp_r x).
apply contains_zero with (1 := H2).
rewrite <- Hx1.
unfold rounding_fixed.
rewrite round_extension_float2.
induction f.
induction Fnum.
unfold round, float2R. simpl.
repeat rewrite Rmult_0_l.
apply refl_equal.
unfold round. simpl.
rewrite round_rexp_exact.
apply refl_equal.
exact (Zle_trans _ _ _ H1 Hx2).
unfold round. simpl.
rewrite round_rexp_exact.
apply refl_equal.
exact (Zle_trans _ _ _ H1 Hx2).
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

Lemma float2_pair_switch :
 forall r : N * Z,
 float2R match r with (n, e) => match n with N0 => Float2 0 0 | Npos m => Float2 (Zpos m) e end end =
 Float2 (Z_of_N (fst r)) (snd r).
intros (n, e).
case n ; intros.
unfold float2R. simpl.
repeat rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
Qed.

Theorem fixed_error_dn :
 forall e : Z, forall x : R, forall zi : FF,
 fixed_error_dn_helper e zi = true ->
 BND (rounding_fixed roundDN e x - x) zi.
intros e x zi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
unfold rounding_fixed.
cutrewrite (Float2 (-1) e = -Float2 1 e :>R)%R in H1.
2: rewrite <- Fopp2_correct ; apply refl_equal.
cut (- Float2 1 e <= round_extension roundDN (fixed_shift e) (good_shift e) x - x <= 0)%R.
intros (H3,H4).
split.
exact (Rle_trans _ _ _ H1 H3).
exact (Rle_trans _ _ _ H4 H2).
generalize (total_order_T 0 x).
intros [[Hx|Hx]|Hx].
generalize (round_extension_prop_pos roundDN (fixed_shift e) (good_shift e) _ Hx).
intros (m1,(m2,(e1,(e2,(H3,(H4,(H5,(H6,H7)))))))).
split.
rewrite H5.
apply Rplus_le_reg_l with (x + Float2 1 e)%R.
rewrite Rplus_assoc.
rewrite Rplus_opp_r. rewrite Rplus_0_r.
rewrite Rplus_assoc.
rewrite Rplus_comm.
unfold Rminus.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l. rewrite Rplus_0_r.
rewrite Rplus_comm.
apply Rle_trans with (1 := proj2 H3).
unfold round. simpl.
rewrite float2_pair_switch.
cutrewrite (Float2 (Z_of_N (fst (round_pos rndZR (fixed_shift e) m2 e2))) (snd (round_pos rndZR (fixed_shift e) m2 e2)) + Float2 1 e =
  Float2 (Z_of_N (fst (round_pos rndZR (fixed_shift e) m2 e2)) + 1) (snd (round_pos rndZR (fixed_shift e) m2 e2)))%R.
apply Rlt_le.
exact (proj2 (round_zr_bound _ (good_shift e) _ _)).
simpl in H7. rewrite <- H7.
unfold fixed_shift at 2 4.
rewrite <- Fplus2_correct.
unfold Fplus2, Fshift2. simpl.
rewrite Zminus_diag.
apply refl_equal.
rewrite H4.
apply Rle_minus.
apply Rle_trans with (2 := proj1 H3).
unfold round. simpl.
rewrite float2_pair_switch.
exact (proj1 (round_zr_bound _ (good_shift e) _ _)).
rewrite <- Hx.
rewrite round_extension_zero.
rewrite Rminus_0_r.
split. 2: apply Rle_refl.
apply Rge_le.
apply Ropp_0_le_ge_contravar.
unfold float2R. simpl.
rewrite Rmult_1_l.
auto with real.
generalize (round_extension_prop_neg roundDN (fixed_shift e) (good_shift e) _ Hx).
cutrewrite (round_dir_mk (rneg roundDN) (rpos roundDN) (rneg_good roundDN) (rpos_good roundDN) = roundUP).
2: apply refl_equal.
intros (m1,(m2,(e1,(e2,(H3,(H4,(H5,(H6,H7)))))))).
unfold Rminus.
split.
rewrite H4. rewrite Fopp2_correct.
apply Rplus_le_reg_l with (round roundUP (fixed_shift e) (Float2 (Zpos m1) e1)).
rewrite <- Rplus_assoc.
rewrite Rplus_opp_r. rewrite Rplus_0_l.
apply Rle_trans with (2 := proj1 H3).
unfold round. simpl.
rewrite float2_pair_switch.
cutrewrite (Float2 (Z_of_N (fst (round_pos rndAW (fixed_shift e) m1 e1))) (snd (round_pos rndAW (fixed_shift e) m1 e1)) + - Float2 1 e =
  Float2 (Z_of_N (fst (round_pos rndAW (fixed_shift e) m1 e1)) - 1) (snd (round_pos rndAW (fixed_shift e) m1 e1)))%R.
apply Rlt_le.
exact (proj1 (round_aw_bound _ (good_shift e) _ _)).
simpl in H6. rewrite <- H6.
unfold fixed_shift at 2 4.
rewrite <- Fopp2_correct.
rewrite <- Fplus2_correct.
unfold Fplus2, Fshift2, Fopp2.
rewrite Zminus_diag.
apply refl_equal.
rewrite H5. rewrite Fopp2_correct.
apply Rplus_le_reg_l with (round roundUP (fixed_shift e) (Float2 (Zpos m2) e2)).
rewrite <- Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_l. rewrite Rplus_0_r.
apply Rle_trans with (1 := proj2 H3).
unfold round. simpl.
rewrite float2_pair_switch.
exact (proj2 (round_aw_bound _ (good_shift e) _ _)).
Qed.

End Gappa_fixed.
