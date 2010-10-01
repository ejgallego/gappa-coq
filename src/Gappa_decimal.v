Require Import Fcore_defs.
Require Import Gappa_common.

Section Gappa_decimal.

Definition Dcompare (x : float2) (y : float10) :=
 let m := Fnum10 y in let e := Fexp10 y in
 match e with
 | Zpos p => Fcomp2 x (Float2 (m * Zpower_pos 5 p) e)
 | Zneg p => Fcomp2 (Float2 (Fnum x * Zpower_pos 5 p) (Fexp x)) (Float2 m e)
 | Z0 => Fcomp2 x (Float2 m 0)
 end.

Lemma pow_exp :
 forall x y : R, forall e : nat,
 (x^e * y^e = (x*y)^e)%R.
intros x y e.
induction e.
apply Rmult_1_l.
repeat rewrite <- tech_pow_Rmult.
rewrite <- IHe.
ring.
Qed.

Lemma Zpower_pos_pos:
 forall x e : positive,
 (0 < Zpower_pos (Zpos x) e)%Z.
intros x e.
rewrite Zpower_pos_nat.
induction (nat_of_P e).
exact (refl_equal Lt).
change (Zpower_nat (Zpos x) (S n)) with ((Zpos x) * Zpower_nat (Zpos x) n)%Z.
apply Zmult_lt_0_compat with (2 := IHn).
exact (refl_equal Lt).
Qed.

Lemma Dcompare_correct :
  forall x : float2, forall y : float10,
  Dcompare x y = Rcompare x y.
Proof.
assert (forall e, Zpower_pos 5 e * Zpower_pos 2 e = Zpower_pos 10 e)%Z.
intros e.
rewrite 3!Zpower_pos_nat.
induction (nat_of_P e).
apply refl_equal.
change ((5 * Zpower_nat 5 n) * (2 * Zpower_nat 2 n) = 10 * Zpower_nat 10 n)%Z.
rewrite <- IHn.
ring.
(* *)
intros x (ym, ye).
unfold Dcompare, float10R. simpl.
destruct ye as [|ye|ye] ; rewrite Fcomp2_correct.
apply refl_equal.
(* . *)
apply f_equal.
unfold float2R, Fcore_defs.F2R. simpl.
rewrite Z2R_mult, Rmult_assoc, <- Z2R_mult.
now apply (f_equal (fun v => Z2R ym * Z2R v)%R).
(* . *)
unfold float2R at 1, F2R at 1. simpl.
replace (Z2R (Fnum x * Zpower_pos 5 ye) * bpow radix2 (Fexp x))%R with (x * Z2R (Zpower_pos 5 ye))%R.
rewrite <- (Rcompare_mult_r (Z2R (Zpower_pos 2 ye))).
rewrite Rmult_assoc, <- Z2R_mult, H.
rewrite <- (Rcompare_mult_r (Z2R (Zpower_pos 10 ye)) x).
apply f_equal.
unfold float2R, F2R. simpl.
rewrite 2!Rmult_assoc, 2!Rinv_l.
apply refl_equal.
apply Rgt_not_eq.
exact (bpow_gt_0 radix10 (Zpos ye)).
apply Rgt_not_eq.
exact (bpow_gt_0 radix2 (Zpos ye)).
exact (bpow_gt_0 radix10 (Zpos ye)).
exact (bpow_gt_0 radix2 (Zpos ye)).
unfold float2R, F2R. simpl.
rewrite Z2R_mult.
ring.
Qed.

Definition Dle_fd (x : float2) (y : float10) :=
 match (Dcompare x y) with
 | Gt => false
 | _ => true
 end.

Lemma Dle_fd_correct :
  forall x : float2, forall y : float10,
  Dle_fd x y = true ->
  (x <= y)%R.
Proof.
intros x y H.
apply Rcompare_not_Gt_inv.
revert H.
unfold Dle_fd.
rewrite Dcompare_correct.
now case Rcompare.
Qed.

Definition Dle_df (x : float10) (y : float2) :=
 match (Dcompare y x) with
 | Lt => false
 | _ => true
 end.

Lemma Dle_df_correct :
  forall x : float10, forall y : float2,
  Dle_df x y = true ->
  (x <= y)%R.
Proof.
intros x y H.
apply Rcompare_not_Lt_inv.
revert H.
unfold Dle_df.
rewrite Dcompare_correct.
now case Rcompare.
Qed.

End Gappa_decimal.
