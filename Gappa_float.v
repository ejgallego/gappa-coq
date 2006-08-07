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
generalize (total_order_T 0 x).
intros [[Hx|Hx]|Hx].
generalize (round_extension_prop_pos rdir (float_shift p k1) (good_shift p k1) _ Hx).
intros (m1,(m2,(e1,(e2,(H1,(H2,(_,(H3,_)))))))).
rewrite H2.
unfold round. simpl.
exists (match round_pos (rpos rdir) (float_shift p k1) m1 e1 with (n,e) =>
  match n with N0 => Float2 0 (-k1) | Npos p => Float2 (Zpos p) e end end).
split.
case (round_pos (rpos rdir) (float_shift p k1) m1 e1) ; intros.
case n ; intros.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
induction (round_pos (rpos rdir) (float_shift p k1) m1 e1).
unfold float_shift in H3. simpl in H3.
rewrite <- H3.
case a ; intros.
exact H.
apply Zle_trans with (1 := H).
exact (Zmax2 _ _).
exists (Float2 0 (-k1)).
split.
rewrite <- Hx.
rewrite round_extension_zero.
unfold float2R. apply Rmult_0_l.
exact H.
generalize (round_extension_prop_neg rdir (float_shift p k1) (good_shift p k1) _ Hx).
intros (m1,(m2,(e1,(e2,(H1,(H2,(_,(H3,_)))))))).
rewrite H2.
unfold round. simpl.
exists (match round_pos (rneg rdir) (float_shift p k1) m1 e1 with (n,e) =>
  match n with N0 => Float2 0 (-k1) | Npos p => Float2 (Zneg p) e end end).
split.
case (round_pos (rneg rdir) (float_shift p k1) m1 e1) ; intros.
case n ; intros.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
induction (round_pos (rneg rdir) (float_shift p k1) m1 e1).
unfold float_shift in H3. simpl in H3.
rewrite <- H3.
case a ; intros.
exact H.
apply Zle_trans with (1 := H).
exact (Zmax2 _ _).
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

End Gappa_float.
