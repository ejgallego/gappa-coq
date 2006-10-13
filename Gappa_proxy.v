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
destruct (Zmax_irreducible_inf (k0 - Zpos p) (-d)).
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
ring (-d - (-d - 1))%Z.
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
ring (-d - (-d - 1))%Z.
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
ring ((Zpos m + 1) * 2 - (Zpos m * 2 + 1))%Z.
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
Admitted.

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
