Require Import Gappa_common.

Section Gappa_pred_fixflt.

Definition fix_of_singleton_bnd_helper (xi : FF) (n : Z) :=
 Zeq_bool (Fnum (lower xi)) (Fnum (upper xi)) &&
 Zeq_bool (Fexp (lower xi)) (Fexp (upper xi)) &&
 Zle_bool n (Fexp (lower xi)).

Lemma Zeq_bool_correct_t :
 forall m n : Z, Zeq_bool m n = true -> (m = n)%Z.
 intros m n.
Admitted.

Theorem fix_of_singleton_bnd :
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
assert (float2R (lower xi) = x).
apply Rle_antisym.
exact (proj1 Hx).
replace (lower xi) with (upper xi).
exact (proj2 Hx).
apply sym_equal.
induction (lower xi). induction (upper xi).
simpl in H1, H2.
rewrite H1.
rewrite H2.
apply refl_equal.
exists (lower xi).
exact (conj H H3).
Qed.

Definition fix_of_flt_bnd_helper (xi : FF) (m : Z) (n : positive) :=
 true. (* ??? TODO *)

Theorem fix_of_flt_bnd :
 forall x : R, forall xi : FF, forall m : Z, forall n : positive,
 FLT x n -> ABS x xi ->
 fix_of_flt_bnd_helper xi m n = true ->
 FIX x m.
intros x xi m n Hxf Hxa Hb.
Admitted.

Theorem flt_of_fix_bnd :
 forall x : R, forall xi : FF, forall m : Z, forall n : positive,
 FIX x m -> ABS x xi ->
 fix_of_flt_bnd_helper xi m n = true ->
 FLT x n.
intros x xi m n Hxf Hxa Hb.
Admitted.

Definition add_fix_helper (xn yn zn : Z) :=
 Zle_bool zn xn &&
 Zle_bool zn yn.

Theorem add_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x + y)%R zn.
intros x y xn yn zn Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
unfold FIX in *.
elim Hx. clear Hx. intros x0 (Rx, Hx).
elim Hy. clear Hy. intros y0 (Ry, Hy).
exists (Fplus2 x0 y0).
split.
rewrite <- Rx.
rewrite <- Ry.
apply Fplus2_correct.
simpl.
case (Zmin_or (Fexp x0) (Fexp y0)) ; intro H ; rewrite H.
apply Zle_trans with (1 := H1) (2 := Hx).
apply Zle_trans with (1 := H2) (2 := Hy).
Qed.

Theorem sub_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x - y)%R zn.
intros x y xn yn zn Hx Hy Hb.
unfold Rminus.
apply add_fix with xn yn.
exact Hx.
elim Hy. clear Hy.
intros y0 (R, Hy).
exists (Fopp2 y0).
split.
rewrite <- R.
apply Fopp2_correct.
apply Hy.
exact Hb.
Qed.

End Gappa_pred_fixflt.
