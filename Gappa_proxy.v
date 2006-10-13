Require Import Gappa_common.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.
Require Import Gappa_round.
Require Import Gappa_float.

Section Gappa_proxy.

Definition float_ulp (p : positive) (d m e : Z) :=
 match m with
 | Zpos n => float_shift p d (e + Zpos (digits n))%Z
 | Zneg n => float_shift p d (e + Zpos (digits n))%Z
 | Z0 => (-d)%Z
 end.

Axiom float_absolute_ne_binade :
 forall p : positive, forall d k : Z, forall x : R,
 (Float2 1 (k - 1) <= x < Float2 1 k)%R ->
 (Rabs (rounding_float roundNE p d x - x) <= Float2 1 (float_shift p d k - 1))%R.

Lemma float_absolute_ne_whole :
 forall p : positive, forall d k : Z, forall x : R,
 (Rabs x < Float2 1 k)%R ->
 (Rabs (rounding_float roundNE p d x - x) <= Float2 1 (float_shift p d k - 1))%R.
intros p d k x H.
cutrewrite (Rabs (rounding_float roundNE p d x - x) = Rabs (rounding_float roundNE p d (Rabs x) - Rabs x))%R.
destruct (Rabs_pos x).
destruct (log2 _ H0) as (k0,Hk).
apply Rle_trans with (Float2 1 (float_shift p d k0 - 1)).
apply float_absolute_ne_binade.
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
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
apply Rle_lt_trans with (Rabs x).
unfold float2R. rewrite Rmult_1_l.
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
clear H.
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
rewrite float2_zero in Hx.
elim (Req_dec x 0) ; intro H.
exact H.
elim Rlt_not_le with (2 := Hx).
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
 Zlt_bool (-d) (Fexp u) &&
 Fle2 u (Float2 (Zpos (xI (shift_pos p xH))) e) &&
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_wide_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS x xi ->
 float_absolute_wide_ne_helper p d xi zi = true ->
 BND (rounding_float roundNE p d x - x) zi.
Admitted.

End Gappa_proxy.
