Require Import Gappa_common.

Section Gappa_pred_rel.

Theorem bnd_of_abs_rel :
 forall a b : R, forall bi zi : FF,
 ABS b bi -> REL a b zi ->
 abs_not_zero bi = true ->
 BND ((a - b) / b) zi.
intros a b bi zi Ha (x,(Hr1,Hr2)) H.
generalize (abs_not_zero_correct _ _ Ha H). clear Ha H. intro H.
cutrewrite ((a - b) / b = x)%R.
exact Hr1.
rewrite Hr2.
field.
exact H.
Qed.

End Gappa_pred_rel.