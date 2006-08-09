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

Definition bnd_of_bnd_fix_helper (xi zi : FF) (e : Z) :=
 Fle2 (lower zi) (round roundUP (fixed_shift e) (lower xi)) &&
 Fle2 (round roundDN (fixed_shift e) (upper xi)) (upper zi).

Theorem bnd_of_bnd_fix :
 forall x : R, forall xn : Z, forall xi zi : FF,
 BND x xi -> FIX x xn ->
 bnd_of_bnd_fix_helper xi zi xn = true ->
 BND x zi.
intros x xn xi zi Hxb (fx,(Hx1,Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). rewrite <- (round_extension_float2 roundUP _ (good_shift xn)). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). rewrite <- (round_extension_float2 roundDN _ (good_shift xn)). clear H2. intro H2.
rewrite <- Hx1.
rewrite <- Hx1 in Hxb.
split.
apply Rle_trans with (1 := H1).
rewrite <- (round_extension_representable roundUP _ (good_shift xn) fx).
apply round_extension_monotone.
exact (proj1 Hxb).
unfold rexp_representable, fixed_shift.
case (Fnum fx) ; trivial.
apply Rle_trans with (2 := H2).
rewrite <- (round_extension_representable roundDN _ (good_shift xn) fx).
apply round_extension_monotone.
exact (proj2 Hxb).
unfold rexp_representable, fixed_shift.
case (Fnum fx) ; trivial.
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
(* *)
generalize (round_extension_prop_pos roundDN (fixed_shift e) (good_shift e) _ Hx).
intros (m1,(m2,(e1,(e2,(H3,(H4,(H5,(H6,H7)))))))).
split.
rewrite H5.
unfold round. simpl.
rewrite tofloat_0.
assert (tofloat (round_pos rndZR (fixed_shift e) m2 e2) - (Float2 (Zpos m2) e2)
  <= tofloat (round_pos rndZR (fixed_shift e) m2 e2) - x)%R.
unfold Rminus.
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
exact (proj2 H3).
apply Rle_trans with (2 := H).
simpl in H7.
clear H H3 H4 H5 H6 Hx H1 H2 x zi m1 e1.
generalize (rexp_case (fixed_shift e) (good_shift e) m2 e2).
intros [H1|[(H1,(H2,(H3,H4)))|(H5,(m,(H1,(H2,(H3,H4)))))]].
rewrite (round_rexp_exact rndZR _ _ _ H1).
rewrite Rminus_diag_eq. 2: apply refl_equal.
apply Rge_le.
apply Ropp_0_le_ge_contravar.
unfold float2R. simpl.
rewrite Rmult_1_l.
auto with real.
apply Rlt_le.
assert (tofloat (round_pos rndZR (fixed_shift e) m2 e2) - Float2 1 (fixed_shift e (e2 + Zpos (digits m2)))
  < tofloat (round_pos rndZR (fixed_shift e) m2 e2) - Float2 (Zpos m2) e2)%R.
unfold Rminus.
apply Rplus_lt_compat_l.
apply Ropp_gt_lt_contravar.
exact H4.
apply Rle_lt_trans with (2 := H).
assert (e2 < fixed_shift e (e2 + Zpos (digits m2)))%Z.
generalize (Zgt_pos_0 (digits m2)).
omega.
rewrite tofloat_pair.
rewrite <- H7.
unfold round_pos. simpl.
rewrite (Zpos_pos_of_Z _ _ H0).
rewrite H3.
simpl.
unfold fixed_shift.
apply Req_le.
unfold float2R.
ring.
apply Rlt_le.
assert (tofloat (round_pos rndZR (fixed_shift e) m2 e2) - Float2 (Zpos m + 1) (fixed_shift e (e2 + Zpos (digits m2)))
  < tofloat (round_pos rndZR (fixed_shift e) m2 e2) - Float2 (Zpos m2) e2)%R.
unfold Rminus.
apply Rplus_lt_compat_l.
apply Ropp_gt_lt_contravar.
exact H4.
apply Rle_lt_trans with (2 := H).
rewrite tofloat_pair.
rewrite <- H7.
unfold round_pos.
rewrite (Zpos_pos_of_Z _ _ (proj1 H5)).
rewrite <- H1.
unfold rndZR, fst, Z_of_N, fixed_shift.
apply Req_le.
rewrite <- Fminus2_correct.
unfold Fminus2, Fshift2.
rewrite Zminus_diag.
unfold Fnum.
ring (Zpos m - (Zpos m + 1))%Z.
unfold float2R. simpl.
auto with real.
(* *)
rewrite H4.
unfold round. simpl.
rewrite tofloat_0.
apply Rplus_le_reg_l with x.
ring (x + (tofloat (round_pos rndZR (fixed_shift e) m1 e1) - x))%R.
rewrite Rplus_0_r.
apply Rle_trans with (2 := proj1 H3).
simpl in H6.
clear H3 H4 H5 H7 Hx H1 H2 x zi m2 e2.
generalize (rexp_case (fixed_shift e) (good_shift e) m1 e1).
intros [H1|[(H1,(H2,(H3,H4)))|(H5,(m,(H1,(H2,(H3,H4)))))]].
rewrite (round_rexp_exact rndZR _ _ _ H1).
apply Rle_refl.
assert (e1 < fixed_shift e (e1 + Zpos (digits m1)))%Z.
generalize (Zgt_pos_0 (digits m1)).
omega.
rewrite tofloat_pair.
rewrite <- H6.
unfold round_pos. simpl.
rewrite (Zpos_pos_of_Z _ _ H).
rewrite H3.
unfold float2R.
simpl.
rewrite Rmult_0_l.
apply Rmult_le_pos ; auto with real.
rewrite tofloat_pair.
rewrite <- H6.
unfold round_pos. simpl.
rewrite (Zpos_pos_of_Z _ _ (proj1 H5)).
rewrite <- H1.
exact H3.
(* *)
rewrite <- Hx.
rewrite round_extension_prop_zero.
unfold float2R.
rewrite Rmult_1_l.
rewrite Rmult_0_l.
rewrite Rminus_0_r.
split. 2: apply Rle_refl.
apply Rge_le.
auto with real.
(* *)
unfold Rminus.
generalize (round_extension_prop_neg roundDN (fixed_shift e) (good_shift e) _ Hx).
cutrewrite (round_dir_mk (rneg roundDN) (rpos roundDN) (rneg_good roundDN) (rpos_good roundDN) = roundUP).
2: apply refl_equal.
intros (m1,(m2,(e1,(e2,(H3,(H4,(H5,(H6,H7)))))))).
split.
rewrite H4. rewrite Fopp2_correct.
unfold round. simpl.
rewrite tofloat_0.
apply Rplus_le_reg_l with (tofloat (round_pos rndAW (fixed_shift e) m1 e1)).
rewrite <- Rplus_assoc.
rewrite Rplus_opp_r. rewrite Rplus_0_l.
apply Rle_trans with (2 := proj1 H3).
simpl in H6.
clear H3 H4 H5 H7 Hx H1 H2 x zi m2 e2.
generalize (rexp_case (fixed_shift e) (good_shift e) m1 e1).
intros [H1|[(H1,(H2,(H3,H4)))|(H5,(m,(H1,(H2,(H3,H4)))))]].
rewrite (round_rexp_exact rndAW _ _ _ H1).
rewrite <- (Rplus_0_r (Float2 (Zpos m1) e1)).
apply Rplus_le_compat_l.
unfold float2R.
rewrite Rmult_1_l.
apply Rge_le.
auto with real.
rewrite tofloat_pair.
rewrite <- H6.
assert (e1 < fixed_shift e (e1 + Zpos (digits m1)))%Z.
generalize (Zgt_pos_0 (digits m1)).
omega.
unfold round_pos. simpl.
rewrite (Zpos_pos_of_Z _ _ H).
rewrite H3.
unfold fixed_shift.
apply Rle_trans with R0.
case (rndAW (shr m1 (pos_of_Z (e - e1))) e).
simpl.
rewrite Rplus_opp_r.
apply Rle_refl.
unfold float2R. simpl.
rewrite Rmult_0_l.
rewrite Rmult_1_l.
rewrite Rplus_0_l.
apply Rge_le.
auto with real.
unfold float2R. simpl.
apply Rmult_le_pos ; auto with real.
rewrite tofloat_pair.
rewrite <- H6.
unfold round_pos. simpl.
rewrite (Zpos_pos_of_Z _ _ (proj1 H5)).
rewrite <- H1.
apply Rle_trans with (2 := H3).
unfold fixed_shift.
case (rndAW (shr m1 (pos_of_Z (e - e1))) e).
simpl.
rewrite Zpos_succ_morphism.
rewrite <- Fopp2_correct.
rewrite <- Fplus2_correct.
unfold Fplus2, Fshift2.
rewrite Zminus_diag.
unfold Fopp2, Fnum, Zsucc.
ring (Zpos m + 1 + -(1))%Z.
apply Rle_refl.
rewrite <- (Rplus_0_r (Float2 (Zpos m) e)).
apply Rplus_le_compat_l.
unfold float2R.
rewrite Rmult_1_l.
apply Rge_le.
auto with real.
(* *)
rewrite H5. rewrite Fopp2_correct.
unfold round. simpl.
rewrite tofloat_0.
apply Rplus_le_reg_l with (tofloat (round_pos rndAW (fixed_shift e) m2 e2)).
rewrite <- Rplus_assoc.
rewrite Rplus_opp_r. rewrite Rplus_0_l.
rewrite Rplus_0_r.
apply Rle_trans with (1 := proj2 H3).
simpl in H7.
clear H3 H4 H5 H6 Hx H1 H2 x zi m1 e1.
generalize (rexp_case (fixed_shift e) (good_shift e) m2 e2).
intros [H1|[(H1,(H2,(H3,H4)))|(H5,(m,(H1,(H2,H3))))]].
rewrite (round_rexp_exact rndAW _ _ _ H1).
apply Rle_refl.
generalize (round_constant_underflow rndAW _ (good_shift e) _ (refl_equal e) m2 e2).
simpl.
intros (Ha,(Hb,Hc)).
unfold fixed_shift in H4.
apply Rlt_le.
generalize (bracket_case_underflow _ _ _ H4).
intros [H0|[H0|H0]].
rewrite (Ha H0).
exact H4.
rewrite (Hb H0).
exact H4.
rewrite (Hc H0).
exact H4.
generalize (round_constant rndAW _ _ _ H2 m2 e2).
simpl.
intros (Ha,(Hb,Hc)).
generalize (bracket_case _ _ _ _ H3).
intros [H0|[H0|[H0|H0]]].
rewrite (round_unicity _ (fixed_shift e) _ _ _ _ rndAW_good H0).
unfold round_pos.
rewrite H2.
rewrite Zminus_diag.
rewrite H0.
apply Rle_refl.
rewrite (Ha H0). simpl.
rewrite Zpos_succ_morphism.
exact (Rlt_le _ _ (proj2 H3)).
rewrite (Hb H0). simpl.
rewrite Zpos_succ_morphism.
exact (Rlt_le _ _ (proj2 H3)).
rewrite (Hc H0). simpl.
rewrite Zpos_succ_morphism.
exact (Rlt_le _ _ (proj2 H3)).
Qed.

End Gappa_fixed.
