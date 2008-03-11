Require Import Reals.
Require Import ZArith.

Section Gappa_integer.

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Definition F2R radix m e :=
  match e with
  | Zpos p => Z2R (m * Zpower_pos (Zpos radix) p)
  | Z0 => Z2R m
  | Zneg p => (Z2R m / Z2R (Zpower_pos (Zpos radix) p))%R
  end.

Lemma P2R_INR :
  forall n, P2R n = INR (nat_of_P n).
induction n ; simpl ; try (
  rewrite IHn ;
  rewrite <- (mult_INR 2) ;
  rewrite <- (nat_of_P_mult_morphism 2) ;
  change (2 * n)%positive with (xO n)).
(* xI *)
rewrite (Rplus_comm 1).
change (nat_of_P (xO n)) with (Pmult_nat n 2).
case n ; intros ; simpl ; try apply refl_equal.
case (Pmult_nat p 4) ; intros ; try apply refl_equal.
rewrite Rplus_0_l.
apply refl_equal.
apply Rplus_comm.
(* xO *)
case n ; intros ; apply refl_equal.
(* xH *)
apply refl_equal.
Qed.

Lemma Z2R_IZR :
  forall n, Z2R n = IZR n.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Lemma opp_Z2R :
  forall m, (Z2R (-m) = - Z2R m)%R.
intros.
repeat rewrite Z2R_IZR.
apply Ropp_Ropp_IZR.
Qed.

Lemma plus_Z2R :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Lemma minus_Z2R :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply sym_eq.
apply Z_R_minus.
Qed.

Lemma mult_Z2R :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Lemma le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Lemma Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Lemma lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Lemma Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
Qed.

Lemma Zpower_pos_powerRZ :
  forall n m,
  Z2R (Zpower_pos n m) = powerRZ (Z2R n) (Zpos m).
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite mult_Z2R.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Lemma F2R_split :
  forall radix m e,
  (F2R radix m e = Z2R m * powerRZ (P2R radix) e)%R.
intros.
unfold F2R.
destruct e.
apply sym_eq.
apply Rmult_1_r.
rewrite mult_Z2R.
rewrite Zpower_pos_powerRZ.
apply refl_equal.
rewrite Zpower_pos_powerRZ.
apply refl_equal.
Qed.

End Gappa_integer.