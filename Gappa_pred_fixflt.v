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
 true. (* TODO *)

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
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
exists (Fplus2 fx fy).
split.
rewrite <- Hx1.
rewrite <- Hy1.
apply Fplus2_correct.
unfold Fplus2, Fshift2.
case (Fexp fx - Fexp fy)%Z ; intros.
exact (Zle_trans _ _ _ H1 Hx2).
exact (Zle_trans _ _ _ H2 Hy2).
exact (Zle_trans _ _ _ H1 Hx2).
Qed.

Theorem sub_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x - y)%R zn.
intros x y xn yn zn Hx (fy,(Hy1,Hy2)) Hb.
unfold Rminus.
apply (add_fix _ (-y) _ yn zn Hx).
exists (Fopp2 fy).
split.
rewrite <- Hy1.
apply Fopp2_correct.
exact Hy2.
exact Hb.
Qed.

Theorem mul_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 Zle_bool zn (xn + yn) = true ->
 FIX (x * y)%R zn.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Fmult2 fx fy).
split.
rewrite <- Hx1. rewrite <- Hy1.
apply Fmult2_correct.
apply Zle_trans with (1 := H1).
exact (Zplus_le_compat _ _ _ _ Hx2 Hy2).
Qed.

Theorem mul_flt :
 forall x y : R, forall xn yn zn : positive,
 FLT x xn -> FLT y yn ->
 Zle_bool (Zpos xn + Zpos yn) (Zpos zn) = true ->
 FLT (x * y)%R zn.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Fmult2 fx fy).
split.
rewrite <- Hx1. rewrite <- Hy1.
apply Fmult2_correct.
apply Zlt_le_trans with (Zpower_nat 2 (nat_of_P xn + nat_of_P yn)).
rewrite Zpower_nat_is_exp.
simpl.
rewrite Zabs_Zmult.
repeat rewrite <- Zpower_pos_nat.
apply Zle_lt_trans with (Zabs (Fnum fx) * Zpower_pos 2 yn)%Z.
exact (Zmult_le_compat_l _ _ _ (Zlt_le_weak _ _ Hy2) (Zabs_pos (Fnum fx))).
apply Zmult_lt_compat_r with (2 := Hx2).
rewrite Zpower_pos_nat.
unfold Zpower_nat.
set (f := fun x0 : Z => (2 * x0)%Z).
induction (nat_of_P yn).
exact (refl_equal _).
simpl.
unfold f at 1.
omega.
rewrite Zpower_pos_nat.
assert (nat_of_P xn + nat_of_P yn <= nat_of_P zn).
case (le_or_lt (nat_of_P xn + nat_of_P yn) (nat_of_P zn)) ; intro.
exact H.
elim (Zle_not_lt _ _ H1).
repeat rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite <- inj_plus.
exact (inj_lt _ _ H).
rewrite (le_plus_minus _ _ H).
generalize (nat_of_P xn + nat_of_P yn).
intros.
rewrite Zpower_nat_is_exp.
pattern (Zpower_nat 2 n) at 1 ; replace (Zpower_nat 2 n) with (Zpower_nat 2 n * 1)%Z.
2: apply Zmult_1_r.
apply Zmult_le_compat_l.
unfold Zpower_nat.
set (f := fun x0 : Z => (2 * x0)%Z).
induction (nat_of_P zn - n).
apply Zle_refl.
simpl.
unfold f at 1.
omega.
apply Zpower_NR0.
compute.
discriminate.
Qed.

End Gappa_pred_fixflt.
