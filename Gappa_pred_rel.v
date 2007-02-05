Require Import Gappa_common.

Section Gappa_pred_rel.

Theorem bnd_of_nzr_rel :
 forall a b : R, forall zi : FF,
 NZR b -> REL a b zi ->
 BND ((a - b) / b) zi.
intros a b zi Hb (x,(_,(Hr1,Hr2))).
cutrewrite ((a - b) / b = x)%R.
exact Hr1.
rewrite Hr2.
field.
exact Hb.
Qed.

Definition mul_rr_helper (xi yi zi : FF) :=
 Flt2 (Float2 (-1) 0) (lower zi) &&
 Fle2 (lower zi) (Fplus2 (Fplus2 (lower xi) (lower yi))
                         (Fmult2 (lower xi) (lower yi))) &&
 Fle2 (Fplus2 (Fplus2 (upper xi) (upper yi))
              (Fmult2 (upper xi) (upper yi))) (upper zi).

Theorem mul_rr :
 forall x1 x2 y1 y2 : R, forall xi yi zi : FF,
 REL x1 x2 xi -> REL y1 y2 yi ->
 mul_rr_helper xi yi zi = true ->
 REL (x1 * y1) (x2 * y2) zi.
intros x1 x2 y1 y2 xi yi zi (xe,(Hx1,(Hx2,Hx3))) (ye,(Hy1,(Hy2,Hy3))) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Flt2_correct _ _ H1).
cutrewrite (Float2 (-1) 0 = -1 :>R)%R.
2: unfold float2R ; auto with real.
clear H1. intro H1.
generalize (Fle2_correct _ _ H2).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H2. intro H2.
generalize (Fle2_correct _ _ H3).
repeat rewrite Fplus2_correct.
rewrite Fmult2_correct. clear H3. intro H3.
exists (xe + ye + xe * ye)%R.
split.
exact H1.
split.
apply IRcompose with (1 := Rlt_le _ _ Hx1) (2 := Rlt_le _ _ Hy1)
 (3 := H2) (4 := H3) (5 := Hx2) (6 := Hy2).
rewrite Hx3.
rewrite Hy3.
ring.
Qed.

End Gappa_pred_rel.