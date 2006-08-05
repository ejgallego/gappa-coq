Require Import Classical.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_pred_bnd.
Require Import Gappa_round_def.
Require Import Gappa_round.

Section Gappa_fixed.

Axiom log2:
 forall x : R, (0 < x)%R ->
 { k : Z | (powerRZ 2 (k - 1) <= x < powerRZ 2 k)%R }.

Axiom plouf : forall P : Prop, P.

Lemma rexp_case_real :
 forall rexp : Z -> Z, good_rexp rexp ->
 forall x : R, (0 < x)%R ->
 { k : Z | rexp k = k /\ (x < Float2 1 k)%R } +
 { e : Z & { m : positive |
  rexp (e + Zpos (digits m))%Z = e /\
  (Float2 (Zpos m) e <= x < Float2 (Zpos m + 1) e)%R }}.
intros rexp Hg x Hx.
generalize (log2 x Hx).
intros (l, H).
case (Z_lt_le_dec (rexp l) l)%Z ; intro H0.
right.
exists (rexp l).
exists (pos_of_Z (up (x * powerRZ 2 (- rexp l)) - 1)).
split.
apply (f_equal rexp).
apply plouf. (* TODO *)
rewrite <- Zpos_pos_of_Z.
unfold float2R. simpl.
split.
apply Rle_trans with (((x * powerRZ 2 (- rexp l) + 1) - 1) * powerRZ 2 (rexp l))%R.
apply Rmult_le_compat_r.
auto with real.
unfold Zminus. rewrite plus_IZR.
unfold Rminus. apply Rplus_le_compat_r.
cutrewrite (IZR (up (x * powerRZ 2 (- rexp l))) = x * powerRZ 2 (- rexp l) +
  (IZR (up (x * powerRZ 2 (- rexp l))) - x * powerRZ 2 (- rexp l)))%R.
2: ring.
apply Rplus_le_compat_l.
exact (proj2 (archimed _)).
unfold Rminus. rewrite Rplus_assoc.
rewrite Rplus_opp_r. rewrite Rplus_0_r.
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
rewrite Zplus_opp_l.
auto with real.
unfold Zminus. rewrite <- Zplus_assoc.
rewrite Zplus_0_r.
apply Rle_lt_trans with (x * powerRZ 2 (- rexp l) * powerRZ 2 (rexp l))%R.
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
rewrite Zplus_opp_l.
auto with real.
apply Rmult_lt_compat_r.
auto with real.
exact (proj1 (archimed _)).
apply lt_IZR.
apply Rle_lt_trans with (x * powerRZ 2 (- rexp l))%R.
2: exact (proj1 (archimed _)).
apply Rle_trans with (x * powerRZ 2 (-l + 1))%R.
apply Rmult_le_reg_l with (powerRZ 2 (l - 1)).
auto with real.
rewrite Rmult_1_r.
rewrite (Rmult_comm x).
rewrite <- Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
ring (l - 1 + (- l + 1))%Z.
rewrite Rmult_1_l.
exact (proj1 H).
apply Rmult_le_compat_l.
exact (Rlt_le _ _ Hx).
assert (-l + 1 <= - rexp l)%Z.
omega.
generalize (float2_Rle_pow2 _ _ H1).
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
intro H2. exact H2.
left.
exists (rexp l).
split.
apply (proj2 (proj2 (Hg l) H0)).
apply Zle_refl.
apply Rlt_le_trans with (1 := proj2 H).
cutrewrite (powerRZ 2 l = Float2 1 l).
apply float2_Rle_pow2 with (1 := H0).
unfold float2R.
auto with real.
Admitted.

Ltac caseEq f := generalize (refl_equal f) ; pattern f at -1 ; case f.

Lemma float2_density :
 forall x y : R, (0 < x < y)%R ->
 { e : Z & { m : positive |
 (x < Float2 (Zpos m) e < y)%R }}.
intros x y H.
generalize (log2 (y - x) (Rlt_Rminus _ _ (proj2 H))).
intros (k, H0).
exists (k - 2)%Z.
exists (pos_of_Z (up (x * powerRZ 2 (- (k - 2))))).
cutrewrite (Zpos (pos_of_Z (up (x * powerRZ 2 (- (k - 2))))) = up (x * powerRZ 2 (- (k - 2)))).
split ; unfold float2R ; simpl.
pattern x at 1 ; replace x with (x * powerRZ 2 (- (k - 2)) * powerRZ 2 (k - 2))%R.
apply Rmult_lt_compat_r.
auto with real.
exact (proj1 (archimed _)).
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
ring (- (k - 2) + (k - 2))%Z.
apply Rmult_1_r.
apply Rle_lt_trans with ((x * powerRZ 2 (- (k - 2)) + 1) * powerRZ 2 (k - 2))%R.
apply Rmult_le_compat_r.
auto with real.
cutrewrite (IZR (up (x * powerRZ 2 (- (k - 2)))) =
  x * powerRZ 2 (- (k - 2)) + (IZR (up (x * powerRZ 2 (- (k - 2))))
  - x * powerRZ 2 (- (k - 2))))%R. 2: ring.
apply Rplus_le_compat_l.
exact (proj2 (archimed _)).
rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
ring (- (k - 2) + (k - 2))%Z.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
cutrewrite (y = x + (y - x))%R. 2: ring.
apply Rplus_lt_compat_l.
apply Rlt_le_trans with (2 := proj1 H0).
assert (k - 2 < k - 1)%Z. omega.
generalize (float2_Rlt_pow2 _ _ H1).
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
intro H2. exact H2.
assert (0 < IZR (up (x * powerRZ 2 (- (k - 2)))))%R.
apply Rlt_trans with (x * powerRZ 2 (- (k - 2)))%R.
apply Rmult_lt_0_compat with (1 := proj1 H).
auto with real.
exact (proj1 (archimed _)).
cutrewrite (R0 = IZR 0) in H1. 2: apply refl_equal.
generalize (lt_IZR _ _ H1).
case (up (x * powerRZ 2 (- (k - 2)))) ; intros.
omega.
apply refl_equal.
generalize (Zlt_neg_0 p).
omega.
Qed.

Lemma round_density :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 good_rexp rexp ->
 forall x : R, (0 < x)%R ->
 { m1 : positive & { m2 : positive &
 { e1 : Z & { e2 : Z |
 let f1 := (Float2 (Zpos m1) e1) in
 let f2 := (Float2 (Zpos m2) e2) in
 (f1 <= x <= f2)%R /\
 round_pos rdir rexp m1 e1 = round_pos rdir rexp m2 e2 /\
 let e1' := snd (round_pos rdir rexp m1 e1) in rexp (e1 + Zpos (digits m1))%Z = e1' /\
 let e2' := snd (round_pos rdir rexp m2 e2) in rexp (e2 + Zpos (digits m2))%Z = e2' }}}}.
intros rdir rexp Hg x Hx.
generalize (rexp_case_real _ Hg _ Hx).
intros [(k,(Hk,Hx1))|(e,(m,(He,Hx1)))].
generalize (total_order_T x (Float2 1 (k - 1))).
intros [[Hx2|Hx2]|Hx2].
generalize (float2_density _ _ (conj Hx Hx2)).
intros (e2,(m2,(H2a,H2b))).
assert (0 < x * /2 < x)%R.
split.
apply Rmult_lt_0_compat with (1 := Hx).
auto with real.
pattern x at 2 ; rewrite <- Rmult_1_r.
pattern R1 at 3 ; rewrite <- Rinv_1.
auto with real.
generalize (float2_density _ _ H).
intros (e1,(m1,(_,H1b))).
clear H.
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ H1b).
exact (Rlt_le _ _ H2a).
generalize (round_constant_underflow rdir _ Hg _ Hk).
intros H.
assert (Float2 (Zpos m1) e1 < Float2 1 (k - 1))%R.
exact (Rlt_trans _ _ _ H1b Hx2).
rewrite (proj1 (H m1 e1) H0).
rewrite (proj1 (H m2 e2) H2b).
clear H H0.
simpl.
split.
apply refl_equal.
split ; apply rexp_underflow with (1 := Hg) (2 := Hk).
apply float2_repartition_underflow.
exact (Rlt_trans _ _ _ H1b Hx1).
apply float2_repartition_underflow.
apply Rlt_trans with (1 := H2b).
apply float2_Rlt_pow2.
omega.
exists xH. exists xH. exists (k - 1)%Z. exists (k - 1)%Z.
split.
rewrite Hx2.
split ; apply Rle_refl.
split.
apply refl_equal.
rewrite (proj1 (proj2 (round_constant_underflow rdir _ Hg _ Hk 1 (k - 1))) (refl_equal _)).
simpl.
ring (k - 1 + 1)%Z.
exact (conj Hk Hk).
generalize (float2_density _ _ (conj Hx Hx1)).
intros (e2,(m2,H2)).
assert (0 < Float2 1 (k - 1))%R.
unfold float2R. simpl.
rewrite Rmult_1_l.
auto with real.
generalize (float2_density _ _ (conj H Hx2)).
intros (e1,(m1,H1)).
clear H.
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ (proj2 H1)).
exact (Rlt_le _ _ (proj1 H2)).
generalize (round_constant_underflow rdir _ Hg _ Hk).
intros H.
assert (Float2 1 (k - 1) < Float2 (Zpos m1) e1 < Float2 1 k)%R.
split. exact (proj1 H1).
exact (Rlt_trans _ _ _ (proj2 H1) Hx1).
rewrite (proj2 (proj2 (H m1 e1)) H0).
clear H0.
assert (Float2 1 (k - 1) < Float2 (Zpos m2) e2 < Float2 1 k)%R.
split. 2: exact (proj2 H2).
exact (Rlt_trans _ _ _ Hx2 (proj1 H2)).
rewrite (proj2 (proj2 (H m2 e2)) H0).
clear H H0.
split.
apply refl_equal.
simpl.
split ; apply rexp_underflow with (1 := Hg) (2 := Hk).
apply float2_repartition_underflow.
exact (Rlt_trans _ _ _ (proj2 H1) Hx1).
apply float2_repartition_underflow.
exact (proj2 H2).
case (Rle_lt_or_eq_dec _ _ (proj1 Hx1)) ; intro Hx2.
generalize (conj Hx2 (proj2 Hx1)). clear Hx1 Hx2. intro Hx1.
generalize (total_order_T x (Float2 (Zpos m * 2 + 1) (e - 1))).
intros [[Hx2|Hx2]|Hx2].
assert (0 < Float2 (Zpos m) e)%R.
unfold float2R. simpl.
apply Rmult_lt_0_compat ; auto with real.
generalize (float2_density _ _ (conj H (proj1 Hx1))).
intros (e1,(m1,(H1a,H1b))).
clear H.
generalize (float2_density _ _ (conj Hx Hx2)).
intros (e2,(m2,(H2a,H2b))).
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ H1b).
exact (Rlt_le _ _ H2a).
generalize (round_constant rdir rexp m e He).
intro H.
rewrite (proj1 (H m1 e1) (conj H1a (Rlt_trans _ _ _ H1b Hx2))).
rewrite (proj1 (H m2 e2) (conj (Rlt_trans _ _ _ (proj1 Hx1) H2a) H2b)).
clear H.
split.
apply refl_equal.
rewrite <- He.
simpl. split.
rewrite (proj2 (float2_repartition _ _ _ _ (conj H1a (Rlt_trans _ _ _ H1b (proj2 Hx1))))).
apply refl_equal.
assert (Float2 (Zpos m2) e2 < Float2 (Zpos m + 1) e)%R.
apply Rlt_trans with (1 := H2b).
rewrite (float2_shift_m1 e).
apply float2_binade_lt.
omega.
rewrite (proj2 (float2_repartition _ _ _ _ (conj (Rlt_trans _ _ _ (proj1 Hx1) H2a) H))).
apply refl_equal.
exists (xI m). exists (xI m). exists (e - 1)%Z. exists (e - 1)%Z.
split.
rewrite Hx2.
rewrite Zmult_comm.
split ; apply Rle_refl.
split.
apply refl_equal.
generalize (proj1 (proj2 (round_constant rdir rexp m e He (xI m) (e - 1)))).
cutrewrite (Zpos (xI m) = Zpos m * 2 + 1)%Z.
2: rewrite Zmult_comm ; apply refl_equal.
intro H. rewrite (H (refl_equal _)).
simpl.
rewrite Zpos_succ_morphism.
unfold Zsucc.
cutrewrite (e - 1 + (Zpos (digits m) + 1) = e + Zpos (digits m))%Z.
2: ring.
rewrite He.
split ; apply refl_equal.
assert (0 < Float2 (Zpos m * 2 + 1) (e - 1))%R.
unfold float2R. simpl.
apply Rmult_lt_0_compat ; auto with real.
generalize (float2_density _ _ (conj H Hx2)).
intros (e1,(m1,(H1a,H1b))).
clear H.
generalize (float2_density _ _ (conj Hx (proj2 Hx1))).
intros (e2,(m2,(H2a,H2b))).
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ H1b).
exact (Rlt_le _ _ H2a).
generalize (round_constant rdir rexp m e He).
intro H.
rewrite (proj2 (proj2 (H m1 e1)) (conj H1a (Rlt_trans _ _ _ H1b (proj2 Hx1)))).
rewrite (proj2 (proj2 (H m2 e2)) (conj (Rlt_trans _ _ _ Hx2 H2a) H2b)).
clear H.
split.
apply refl_equal.
rewrite <- He.
simpl. split.
assert (Float2 (Zpos m) e < Float2 (Zpos m1) e1 < Float2 (Zpos m + 1) e)%R.
split.
apply Rlt_trans with (2 := H1a).
rewrite (float2_shift_m1 e).
apply float2_binade_lt.
omega.
exact (Rlt_trans _ _ _ H1b (proj2 Hx1)).
rewrite (proj2 (float2_repartition _ _ _ _ H)).
apply refl_equal.
rewrite (proj2 (float2_repartition _ _ _ _ (conj (Rlt_trans _ _ _ (proj1 Hx1) H2a) H2b))).
apply refl_equal.
exists m. exists m. exists e. exists e.
split.
rewrite Hx2.
split ; apply Rle_refl.
split.
apply refl_equal.
unfold round_pos.
rewrite He.
rewrite Zminus_diag.
split ; apply refl_equal.
Qed.

Lemma round_zero :
 forall rdir : round_dir,
 forall rexp : Z -> Z,
 forall e : Z,
 (round rdir rexp (Float2 Z0 e) = 0 :>R)%R.
intros rdir rexp e.
unfold round, float2R.
simpl.
auto with real.
Qed.

Lemma round_neg :
 forall rdir : round_dir,
 forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 round rdir rexp (Float2 (Zneg m) e) = Fopp2 (round
   (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir))
   rexp (Fopp2 (Float2 (Zneg m) e))).
intros rdir rexp m e.
unfold round, Fopp2.
simpl.
case (round_pos (rneg rdir) rexp m e) ; intros.
case n ; trivial.
Qed.

Lemma round_ext :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 good_rdir rdir -> good_rexp rexp ->
 forall x : R, float2.
intros rdir rexp Hgd Hge x.
generalize (total_order_T 0 x).
intros [[Hx|_]|_].
generalize (round_density rdir rexp Hge x Hx).
intros (m1,(m2,(e1,(e2,H)))).
exact (match round_pos rdir rexp m1 e1 with (m,e) => Float2 (Z_of_N m) e end).
exact (Float2 0 0).
exact (Float2 0 0).
Defined.

Lemma round_ext_positive :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall Hgd : good_rdir rdir, forall Hge : good_rexp rexp,
 forall x : R,
 (0 <= round_ext rdir rexp Hgd Hge x)%R.
intros rdir rexp Hgd Hge x.
unfold round_ext, float2R.
generalize (total_order_T 0 x).
intros [[Hx|_]|_] ; simpl ; try (rewrite Rmult_0_l ; apply Rle_refl).
generalize (round_density rdir rexp Hge x Hx).
intros (m1,(m2,(e1,(e2,_)))).
unfold round_pos.
case (rexp (e1 + Zpos (digits m1)) - e1)%Z ; intros ; simpl.
apply Rmult_le_pos ; auto with real.
case (if rdir (shr m1 p) (rexp (e1 + Zpos (digits m1))%Z)
      then Nsucc (rnd_m (shr m1 p)) else rnd_m (shr m1 p)) ; intros.
rewrite Rmult_0_l.
apply Rle_refl.
apply Rmult_le_pos ; simpl ; auto with real.
apply Rmult_le_pos ; auto with real.
Qed.

Lemma round_ext_monotone :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall Hgd : good_rdir rdir, forall Hge : good_rexp rexp,
 let fext := round_ext rdir rexp Hgd Hge in
 forall x y : R, forall Hb : (0 < x <= y)%R,
 (fext x (proj1 Hb) <= fext y (Rlt_le_trans _ _ _ (proj1 Hb) (proj2 Hb)))%R.
simpl.
intros rdir rexp Hgd Hge x y Hb.
unfold round_ext.
generalize (round_density rdir rexp Hge y (Rlt_le_trans 0 x y (proj1 Hb) (proj2 Hb))).
generalize (round_density rdir rexp Hge x (proj1 Hb)).
intros (mx1,(mx2,(ex1,(ex2,(Hx1,(Hx2,_)))))).
intros (my1,(my2,(ey1,(ey2,(Hy1,(Hy2,_)))))).
rewrite Hy2.
apply (round_monotone _ _ Hgd Hge).
apply Rle_trans with (1 := proj1 Hx1).
exact (Rle_trans _ _ _ (proj2 Hb) (proj2 Hy1)).
Qed.

Lemma round_extension :
 forall rdir : round_dir, forall rexp : Z -> Z,
 good_rexp rexp ->
 forall x : R, float2.
intros rdir rexp Hge x.
generalize (total_order_T x 0).
intros [[Hx|Hx]|Hx].
assert (0 < -x)%R. auto with real.
exact (Fopp2 (round_ext (rneg rdir) rexp (rneg_good rdir) (Hge) (-x) H)).
exact (Float2 0 0).
exact (round_ext (rpos rdir) rexp (rpos_good rdir) (Hge) x Hx).
Defined.

Lemma round_extension_pos :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x : R, forall Hx : (0 < x)%R,
 round_extension rdir rexp Hge x = round_ext (rpos rdir) rexp (rpos_good rdir) Hge x Hx :>R.
intros rdir rexp Hge x Hx.
unfold round_extension.
generalize (total_order_T x 0).
intros [[H|H]|H].
elim (Rlt_irrefl _ (Rlt_trans _ _ _ H Hx)).
assert (0 < x)%R. exact Hx.
rewrite H in H0.
elim (Rlt_irrefl _ H0).
unfold round_ext.
generalize (round_density (rpos rdir) rexp Hge x H).
intros (m1,(m2,(e1,(e2,(H1,(H2,_)))))).
generalize (round_density (rpos rdir) rexp Hge x Hx).
intros (m3,(m4,(e3,(e4,(H3,(H4,_)))))).
apply Rle_antisym.
rewrite H4.
apply round_monotone with (1 := rpos_good rdir) (2 := Hge).
exact (Rle_trans _ _ _ (proj1 H1) (proj2 H3)).
rewrite H2.
apply round_monotone with (1 := rpos_good rdir) (2 := Hge).
exact (Rle_trans _ _ _ (proj1 H3) (proj2 H1)).
Qed.

Lemma round_extension_neg :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x : R, forall Hx : (0 > x)%R,
 round_extension rdir rexp Hge x = Ropp (round_ext (rneg rdir) rexp (rneg_good rdir) Hge (-x) (Ropp_0_gt_lt_contravar x Hx)) :>R.
intros rdir rexp Hge x Hx.
unfold round_extension.
generalize (total_order_T x 0).
intros [[H|H]|H].
unfold round_ext.
generalize (round_density (rneg rdir) rexp Hge (-x) (Ropp_0_gt_lt_contravar x H)).
intros (m1,(m2,(e1,(e2,(H1,(H2,_)))))).
generalize (round_density (rneg rdir) rexp Hge (-x) (Ropp_0_gt_lt_contravar x Hx)).
intros (m3,(m4,(e3,(e4,(H3,(H4,_)))))).
rewrite Fopp2_correct.
apply Ropp_eq_compat.
apply Rle_antisym.
rewrite H4.
apply round_monotone with (1 := rneg_good rdir) (2 := Hge).
exact (Rle_trans _ _ _ (proj1 H1) (proj2 H3)).
rewrite H2.
apply round_monotone with (1 := rneg_good rdir) (2 := Hge).
exact (Rle_trans _ _ _ (proj1 H3) (proj2 H1)).
assert (0 > x)%R. exact Hx.
rewrite H in H0.
elim (Rlt_irrefl _ H0).
elim (Rlt_irrefl _ (Rlt_trans _ _ _ H Hx)).
Qed.

Lemma round_extension_zero :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 round_extension rdir rexp Hge R0 = R0 :>R.
intros rdir rexp Hge.
unfold round_extension.
generalize (total_order_T 0 0).
intros [[H|H]|H].
elim (Rlt_irrefl _ H).
unfold float2R. simpl.
apply Rmult_0_l.
elim (Rlt_irrefl _ H).
Qed.

Lemma round_extension_monotone :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x y : R, (x <= y)%R ->
 (round_extension rdir rexp Hge x <= round_extension rdir rexp Hge y)%R.
intros rdir rexp Hge x y H.
generalize (total_order_T 0 y).
generalize (total_order_T 0 x).
intros [[Hx|Hx]|Hx] [[Hy|Hy]|Hy].
rewrite (round_extension_pos rdir _ Hge _ Hx).
rewrite (round_extension_pos rdir _ Hge _ Hy).
apply round_ext_monotone.
Admitted.

Lemma round_extension_float2 :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall f : float2,
 round_extension rdir rexp Hge f = round rdir rexp f :>R.
intros rdir rexp Hge f.
unfold round_extension.
cutrewrite (f = Float2 (Fnum f) (Fexp f)).
2: induction f ; apply refl_equal.
case (Fnum f) ; intros.
generalize (total_order_T (Float2 0 (Fexp f)) 0).
unfold round. simpl.
intros [[Hf|Hf]|Hf].
elim Rlt_not_le with (1 := Hf).
unfold float2R. rewrite Rmult_0_l.
apply Rle_refl.
apply refl_equal.
elim Rlt_not_le with (1 := Hf).
unfold float2R. rewrite Rmult_0_l.
apply Rle_refl.
generalize (total_order_T (Float2 (Zpos p) (Fexp f)) 0).
unfold round. simpl.
intros [[Hf|Hf]|Hf].
elim Rlt_not_le with (1 := Hf).
unfold float2R. simpl.
apply Rmult_le_pos ; auto with real.
elim Rgt_not_eq with (2 := Hf).
unfold float2R. simpl.
unfold Rgt.
apply Rmult_lt_0_compat ; auto with real.
unfold round_ext.
generalize (round_density (rpos rdir) rexp Hge (Float2 (Zpos p) (Fexp f)) Hf).
intros (m1,(m2,(e1,(e2,(H1,(H2,_)))))).
assert (H': forall m : positive, forall e : Z,
  float2R match round_pos (rpos rdir) rexp m e with (n, e) =>
  match n with
  | N0 => Float2 0 0
  | Npos p0 => Float2 (Zpos p0) e
  end end =
  match round_pos (rpos rdir) rexp m e with (n, e) => float2R (Float2 (Z_of_N n) e) end).
intros m e.
induction (round_pos (rpos rdir) rexp m e).
case a ; intros.
unfold float2R.
repeat rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
apply Rle_antisym.
repeat rewrite H'.
apply (round_monotone _ _ (rpos_good rdir) Hge).
exact (proj1 H1).
repeat rewrite H'.
rewrite H2.
apply (round_monotone _ _ (rpos_good rdir) Hge).
exact (proj2 H1).
generalize (total_order_T (Float2 (Zneg p) (Fexp f)) 0).
unfold round. simpl.
intros [[Hf|Hf]|Hf].
unfold round_ext.
generalize (round_density (rneg rdir) rexp Hge (- Float2 (Zneg p) (Fexp f)) (Ropp_0_gt_lt_contravar (Float2 (Zneg p) (Fexp f)) Hf)).
intros (m1,(m2,(e1,(e2,(H1,(H2,_)))))).
assert (H': forall m : positive, forall e : Z,
  float2R match round_pos (rneg rdir) rexp m e with (n, e) =>
  match n with
  | N0 => Float2 0 0
  | Npos p0 => Float2 (Zneg p0) e
  end end =
  Ropp match round_pos (rneg rdir) rexp m e with (n, e) => float2R (Float2 (Z_of_N n) e) end).
intros m e.
induction (round_pos (rneg rdir) rexp m e).
case a ; intros.
unfold float2R.
repeat rewrite Rmult_0_l.
exact (sym_eq Ropp_0).
rewrite <- Fopp2_correct.
apply refl_equal.
rewrite <- Fopp2_correct in H1.
apply Rle_antisym.
repeat rewrite H'.
apply Ropp_le_contravar.
rewrite H2.
apply (round_monotone _ _ (rneg_good rdir) Hge).
exact (proj2 H1).
repeat rewrite H'.
apply Ropp_le_contravar.
apply (round_monotone _ _ (rneg_good rdir) Hge).
exact (proj1 H1).
elim Rlt_not_eq with (2 := Hf).
unfold float2R. simpl.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_gt_0_contravar.
unfold Rgt.
apply Rmult_lt_0_compat ; auto with real.
elim Rlt_not_le with (1 := Hf).
unfold float2R. simpl.
rewrite Ropp_mult_distr_l_reverse.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
apply Rmult_le_pos ; auto with real.
Qed.

(*
Axiom round_extension :
 forall rdir : round_dir, forall rexp : Z -> Z,
 good_rexp rexp ->
 sigT (fun fext : R -> R =>
 (forall x y : R, (fext x <= fext y)%R) /\
 (forall f : float2, fext f = round rdir rexp f) /\
 (forall x : R, (0 < x)%R ->
  exists m1 : positive, exists m2 : positive,
  exists e1 : Z, exists e2 : Z,
  let f1 := (Float2 (Zpos m1) e1) in
  let f2 := (Float2 (Zpos m2) e2) in
  (f1 <= x <= f2)%R /\ 
  (fext x = round rdir rexp f1 /\ let e1 := Fexp (round rdir rexp f1) in rexp e1 = e1) /\
  (fext x = round rdir rexp f2 /\ let e2 := Fexp (round rdir rexp f2) in rexp e2 = e2))).
*)

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
unfold FIX.
unfold rounding_fixed.
unfold round_extension.
generalize (total_order_T x 0).
intros [[Hx|Hx]|Hx].
unfold round_ext.
generalize (round_density (rneg rdir) (fixed_shift k1) (good_shift k1) (- x) (Ropp_0_gt_lt_contravar x Hx)).
intros (m1,(m2,(e1,(e2,(H1,(H2,(H3,H4))))))).
exists (match round_pos (rneg rdir) (fixed_shift k1) m1 e1 with (n,e) =>
  match n with
  | N0 => Float2 0 k1
  | Npos p => Float2 (Zneg p) e
  end end).
caseEq (round_pos (rneg rdir) (fixed_shift k1) m1 e1).
intros n z.
case n.
intros _.
split.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
exact H.
intros p H0.
split. apply refl_equal.
cutrewrite (z = fixed_shift k1 (e1 + Zpos (digits m1))).
exact H.
rewrite H3.
generalize H0.
case (round_pos (rneg rdir) (fixed_shift k1) m1 e1).
intros. rewrite H5. apply refl_equal.
exists (Float2 0 k1).
split.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
exact H.
unfold round_ext.
generalize (round_density (rpos rdir) (fixed_shift k1) (good_shift k1) x Hx).
intros (m1,(m2,(e1,(e2,(H1,(H2,(H3,H4))))))).
exists (match round_pos (rpos rdir) (fixed_shift k1) m1 e1 with (n,e) =>
  match n with
  | N0 => Float2 0 k1
  | Npos p => Float2 (Zpos p) e
  end end).
caseEq (round_pos (rpos rdir) (fixed_shift k1) m1 e1).
intros n z.
case n.
intros _.
split.
unfold float2R. repeat rewrite Rmult_0_l.
apply refl_equal.
exact H.
intros p H0.
split. apply refl_equal.
cutrewrite (z = fixed_shift k1 (e1 + Zpos (digits m1))).
exact H.
rewrite H3.
generalize H0.
case (round_pos (rpos rdir) (fixed_shift k1) m1 e1).
intros. rewrite H5. apply refl_equal.
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
unfold round, float2R.
simpl.
ring.
unfold round.
simpl.
rewrite round_rexp_exact.
apply refl_equal.
exact (Zle_trans _ _ _ H1 Hx2).
unfold round.
simpl.
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
intros (fext,(H3,(H4,H5))).
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
cutrewrite (R0 = Float2 0 0).
rewrite H4.
apply refl_equal.
unfold float2R. simpl.
apply sym_eq.
apply Rmult_0_l.
generalize (H5 x H0).
intros (f1,(f2,(H8,(H9,H10)))).
split.
apply Rle_trans with (2 := proj1 H8).
rewrite (proj1 H9).
clear H10 H9 H8 f2 H0 H5 H4 H3 fext H2 H1 zi x.
cutrewrite (f1 = Float2 (Fnum f1) (Fexp f1)).
2: induction f1 ; apply refl_equal.
case (Fnum f1) ; intros.
unfold round, float2R. simpl.
repeat rewrite Rmult_0_l.
apply Rle_refl.
unfold round. simpl.
apply Rle_trans with (2 := proj1 (round_zr_bound _ (good_shift e) p (Fexp f1))).
case (round_pos rndZR (fixed_shift e) p (Fexp f1)).
intros.
case n ; intros. 2: apply Rle_refl.
unfold float2R. simpl.
repeat rewrite Rmult_0_l.
apply Rle_refl.
rewrite round_neg.
rewrite Fopp2_correct.
cutrewrite (Float2 (Zneg p) (Fexp f1) = - Float2 (Zpos p) (Fexp f1) :>R)%R.
apply Ropp_le_contravar.
unfold round. simpl.
case (round_pos rndAW (fixed_shift e) p (Fexp f1)).
intros.
case n ; intros. 2: apply Rle_refl.
unfold float2R ; simpl.
repeat rewrite Rmult_0_l.
apply Rle_refl.
unfold round. simpl.


rewrite H8.
replace f with (Float2 (Fnum f) (Fexp f)). 2: induction f ; apply refl_equal.
rewrite H9.
unfold fixed_shift.
cutrewrite (Float2 (Fnum f) e + Float2 1 e = Float2 (Fnum f + 1) e)%R.
generalize (H6 x).
intros (f1, (f2, (H10, H11))).
repeat rewrite H4 in H11.
split.
apply Rle_trans with (2 := proj1 H10).
Admitted.

End Gappa_fixed.
