Require Export Gappa_real.
Require Export Gappa_dyadic.
Require Import ZArith.
Require Export Reals.

Section Gappa_common.

Record FF: Set := makepairF { lower : float2 ; upper : float2 }.

Definition BND (x : R) (xi : FF) :=
 (lower xi <= x <= upper xi)%R.
Definition ABS (x : R) (xi : FF) :=
 (0 <= lower xi)%R /\ (lower xi <= Rabs x <= upper xi)%R.
Definition FIX (x : R) (n : Z) :=
 exists f : float2, float2R f = x /\ (n <= Fexp f)%Z.
Definition FLT (x : R) (n : positive) :=
 exists f : float2, float2R f = x /\ (Zabs (Fnum f) < Zpower_pos 2 n)%Z.

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

Definition contradiction := forall P, P.

End Gappa_common.
