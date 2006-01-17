Require Import Float.
Require Import Gappa_common.

Section Gappa_pred_fixflt.

Definition fix_of_singleton_bnd_helper (xi : FF) (n : Z) :=
 Zeq_bool (Fnum (lower xi)) (Fnum (upper xi)) &&
 Zeq_bool (Fexp (lower xi)) (Fexp (upper xi)) &&
 Zle_bool n (Fexp (lower xi)).

Lemma Zeq_bool_correct_t :
 forall m n : Z, Zeq_bool n m = true -> (m = n)%Z.
 intros m n.
Admitted.

Theorem fix_of_singleton_bnd:
 forall x : R, forall xi : FF, forall n : Z,
 BND x xi ->
 fix_of_singleton_bnd_helper xi n = true ->
 FIX x n.
intros x xi n Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zeq_bool_correct_t _ _ H1). clear H1. intro H1.
generalize (Zeq_bool_correct_t _ _ H2). clear H2. intro H2.
generalize (Zle_bool_imp_le _ _ H3). clear H3. intro H3.
assert (x = lower xi)%R.
apply Rle_antisym.
replace (lower xi) with (upper xi).
exact (proj2 Hx).
apply floatEq ; assumption.
exact (proj1 Hx).
unfold FIX.
exists (lower xi).
exact (conj H H3).
Qed.

End Gappa_pred_fixflt.
