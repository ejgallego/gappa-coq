Require Import Reals.
Require Import IA_real.

Section IA_error.

Definition EabsoluteR (xi : RR) (xr xa : R) :=
 IintR xi (xr - xa)%R.

Definition IunR := (makepairR 1 1).

Definition Iplus1R (xi : RR) :=
 IplusR_fun IunR xi.

Definition ErelativeR (xi : RR) (xr xa : R) :=
 (-1 < lower xi)%R /\ (xa <> 0)%R /\ IintR (Iplus1R xi) (xr / xa)%R.

Lemma Eabs_plusR:
 forall xi yi zi : RR, forall xr xa yr ya : R,
 IplusR_property xi yi zi ->
 EabsoluteR xi xr xa -> EabsoluteR yi yr ya ->
 EabsoluteR zi (xr + yr) (xa + ya).
intros xi yi zi xr xa yr ya Hz Hx Hy.
unfold EabsoluteR in *.
replace (xr + yr - (xa + ya))%R with ((xr - xa) + (yr - ya))%R. 2: ring.
apply Hz; trivial.
Qed.

Lemma Erel_multR:
 forall xi yi zi : RR, forall xr xa yr ya : R,
 ImultR_property (Iplus1R xi) (Iplus1R yi) (Iplus1R zi) ->
 (-1 < lower zi)%R ->
 ErelativeR xi xr xa -> ErelativeR yi yr ya ->
 ErelativeR zi (xr * yr) (xa * ya).
intros xi yi zi xr xa yr ya Hz Hzl (Hxl, (Hx0, Hx)) (Hyl, (Hy0, Hy)).
unfold ErelativeR in *.
split. exact Hzl.
split.
apply prod_neq_R0; trivial.
replace (xr * yr / (xa * ya))%R with ((xr / xa) * (yr / ya))%R.
apply Hz; trivial.
field.
repeat apply prod_neq_R0; trivial.
Qed.

Lemma relative_zero:
 forall xi : RR, forall xr xa : R,
 ErelativeR xi xr xa -> (xr <> 0)%R.
intros xi xr xa (Hl1, (H0, (Hl, Hu))).
assert (0 < xr / xa)%R.
unfold Iplus1R in Hl. simpl in Hl.
apply Rlt_le_trans with (1 + lower xi)%R. 2: exact Hl.
apply Rplus_lt_reg_r with (-1)%R.
rewrite Rplus_0_r with (-1)%R.
replace (-1 + (1 + lower xi))%R with (lower xi). 2: ring.
exact Hl1.
unfold Rdiv in H.
intro H1.
rewrite H1 in H.
assert (0 < 0)%R.
2: apply (Rlt_asym 0 0); exact H2.
pattern R0 at 2; replace R0 with (0 * /xa)%R.
exact H.
apply Rmult_0_l.
Qed.

Lemma Erel_divR:
 forall xi yi zi : RR, forall xr xa yr ya : R,
 IdivR_property (Iplus1R xi) (Iplus1R yi) (Iplus1R zi) ->
 (-1 < lower zi)%R ->
 ErelativeR xi xr xa -> ErelativeR yi yr ya ->
 ErelativeR zi (xr / yr) (xa / ya).
intros xi yi zi xr xa yr ya Hz Hzl (Hxl, (Hx0, Hx)) (Hyl, (Hy0, Hy)).
unfold ErelativeR in *.
split. exact Hzl.
assert (/ya <> 0)%R.
exact (Rinv_neq_0_compat _ Hy0).
split.
unfold Rdiv.
apply prod_neq_R0; trivial.
replace (xr / yr / (xa / ya))%R with ((xr / xa) / (yr / ya))%R.
apply Hz; trivial.
field.
exact Hy0.
assert (yr <> 0)%R.
exact (relative_zero _ _ _ (conj Hyl (conj Hy0 Hy))).
repeat apply prod_neq_R0; trivial.
Qed.

End IA_error.
