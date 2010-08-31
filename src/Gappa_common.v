Require Export Bool.
Require Export ZArith.
Require Export Reals.
Require Export Fcore_Raux.
Require Export Gappa_real.
Require Export Gappa_definitions.
Require Export Gappa_dyadic.

Section Gappa_common.

Lemma Zeq_bool_correct_t :
 forall m n : Z, Zeq_bool m n = true -> (m = n)%Z.
intros m n H.
apply Zcompare_Eq_eq.
unfold Zeq_bool in H.
induction (m ?= n)%Z ; try discriminate.
exact (refl_equal _).
Qed.

Lemma Zlt_bool_correct_t :
 forall m n : Z, Zlt_bool m n = true -> (m < n)%Z.
intros m n H.
generalize (Zlt_cases m n).
rewrite H.
trivial.
Qed.

End Gappa_common.
