Require Import Gappa_common.
Require Import Gappa_round.

Section Gappa_proxy.

Theorem fix_of_flt_bnd :
 forall x : R, forall xi : FF, forall n : Z, forall p : positive,
 FLT x p -> ABS x xi ->
 Zle_bool (n + Zpos p) (Zpos (digits (pos_of_Z (Fnum (lower xi)))) + Fexp (lower xi))
 && Fpos (lower xi) = true ->
 FIX x n.
intros x xi n p (f,(Hx1,Hx2)) Hxi Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
exists f.
split.
exact Hx1.
apply Znot_gt_le.
intro H0.
apply Zle_not_gt with (1 := H1).
clear H1.
apply Zlt_gt.
apply Zlt_le_trans with (Zpos p + Fexp f)%Z.
2: omega.
clear H0 n.
apply Zlt_le_trans with (Zpos (digits (pos_of_Z (Zabs (Fnum f)))) + Fexp f)%Z.
Focus 2.
apply Zplus_le_compat_r.
apply digits_pow2.
cutrewrite (Zpos (pos_of_Z (Zabs (Fnum f))) = Zabs (Fnum f))%Z.
exact Hx2.
assert (0< Zabs (Fnum f))%Z.
apply lt_IZR.
apply Rmult_lt_reg_l with (powerRZ 2 (Fexp f)).
auto with real.
rewrite Rmult_0_r.
apply Rlt_le_trans with (1 := H2).
cutrewrite (powerRZ 2 (Fexp f) * IZR (Zabs (Fnum f)) = Rabs x)%R.
exact (proj1 (proj2 Hxi)).
rewrite <- Hx1.
clear Hx2 Hx1.
induction f.
unfold float2R. simpl.
rewrite Rabs_mult.

induction (Zabs (Fnum f)) ; intros.
elim Zlt_irrefl with (1 := H).
exact Hx2.
generalize (Zlt_neg_0 p0).
omega.
apply lt_IZR.
omega.

generalize float2_digits_correct.

Admitted.

End Gappa_proxy.
