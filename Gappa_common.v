Require Export ZArith.
Require Export Reals.
Require Export Gappa_real.
Require Export Gappa_definitions.
Require Export Gappa_dyadic.

Section Gappa_common.

Definition abs_not_zero (zi : FF) := Fpos (lower zi).

Lemma abs_not_zero_correct :
 forall z : R, forall zi : FF,
 ABS z zi ->
 abs_not_zero zi = true ->
 (z <> 0)%R.
intros z zi Hz Hb. 
generalize (Fpos_correct _ Hb). clear Hb. intro H.
case (Rcase_abs z) ; intro.
apply Rlt_not_eq with (1 := r).
rewrite <- (Rabs_right z r).
apply Rgt_not_eq.
apply Rlt_le_trans with (1 := H) (2 := proj1 (proj2 Hz)).
Qed.

Lemma Zeq_bool_correct_t :
 forall m n : Z, Zeq_bool m n = true -> (m = n)%Z.
 intros m n.
Admitted.

End Gappa_common.
