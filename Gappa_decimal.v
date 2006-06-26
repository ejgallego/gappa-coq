Require Import Gappa_dyadic.
Require Import ZArith.
Require Import Reals.

Section Gappa_decimal.

Record float10 : Set := Float10 { Fnum10 : Z ; Fexp10 : Z }.
Coercion float10R := fun x : float10 => (IZR (Fnum10 x) * powerRZ 10 (Fexp10 x))%R.

Definition Dcompare (x : float2) (y : float10) :=
 let m := Fnum10 y in let e := Fexp10 y in
 match e with
 | Zpos p => Fcomp2 x (Float2 (m * Zpower_pos 5 p) e)
 | Zneg p => Fcomp2 (Float2 (Fnum x * Zpower_pos 5 p) (Fexp x)) (Float2 m e)
 | Z0 => Fcomp2 x (Float2 m 0)
 end.

Ltac caseEq f := generalize (refl_equal f) ; pattern f at -1 ; case f.

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
replace (Zpower_nat (Zpos x) (S n)) with ((Zpos x) * Zpower_nat (Zpos x) n)%Z.
2: apply refl_equal.
apply Zmult_lt_0_compat with (2 := IHn).
exact (refl_equal Lt).
Qed.

Lemma Dcompare_correct :
 forall x : float2, forall y : float10,
 match (Dcompare x y) with
 | Lt => (x < y)%R
 | Eq => (float2R x = y)%R
 | Gt => (x > y)%R
 end.
intros x y.
unfold Dcompare.
case y. intros ym ye.
simpl.
induction ye ; unfold float10R ; simpl.
rewrite Rmult_1_r.
replace (IZR ym) with (float2R (Float2 ym 0)).
2: unfold float2R ; auto with real.
unfold float2R.
caseEq (Fcomp2 x (Float2 ym 0)) ; intro H.
apply Fcomp2_Eq with (1 := H).
apply Fcomp2_Lt with (1 := H).
apply Fcomp2_Gt with (1 := H).
unfold float2R.
assert (H0: (Float2 (ym * Zpower_pos 5 p) (Zpos p) = (IZR ym * 10 ^ nat_of_P p)%R :>R)).
unfold float2R.
simpl.
rewrite mult_IZR.
rewrite Zpower_pos_nat.
replace 5%Z with (Z_of_nat 5). 2: apply refl_equal.
rewrite Zpower_nat_powerRZ.
unfold powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite Rmult_assoc.
rewrite pow_exp.
apply Rmult_eq_compat_l.
replace (INR 5 * 2)%R with 10%R.
apply refl_equal.
simpl. ring.
caseEq (Fcomp2 x (Float2 (ym * Zpower_pos 5 p) (Zpos p))) ;
 intro H ;
 [ generalize (Fcomp2_Eq _ _ H) |
   generalize (Fcomp2_Lt _ _ H) |
   generalize (Fcomp2_Gt _ _ H) ] ;
 clear H ; rewrite H0 ; trivial.
replace 10%R with (IZR 5 * 2)%R.
2: simpl ; ring.
rewrite <- pow_exp.
rewrite Rinv_mult_distr ; try apply pow_nonzero.
2: apply not_O_IZR ; discriminate.
2: apply Rgt_not_eq ; unfold Rgt ; auto with real.
rewrite Rmult_comm.
rewrite Rmult_assoc.
replace (float2R x) with ((/ IZR 5 ^ nat_of_P p) * (x * (IZR 5 ^ nat_of_P p)))%R.
2: field ; apply pow_nonzero ; apply not_O_IZR ; discriminate.
replace (IZR 5 ^ nat_of_P p)%R with (IZR (Zpower_pos 5 p)).
rewrite <- (Rmult_comm (IZR ym)).
assert (Hd: (0 < / IZR (Zpower_pos 5 p))%R).
apply Rinv_0_lt_compat.
replace R0 with (IZR 0). 2: apply refl_equal.
apply IZR_lt.
apply Zpower_pos_pos.
assert (He: (IZR (Fnum x) * powerRZ 2 (Fexp x) * IZR (Zpower_pos 5 p)
 = IZR (Fnum x) * IZR (Zpower_pos 5 p) * powerRZ 2 (Fexp x))%R).
ring.
caseEq (Fcomp2 (Float2 (Fnum x * Zpower_pos 5 p) (Fexp x)) (Float2 ym (Zneg p))) ;
 intro H ;
 [ generalize (Fcomp2_Eq _ _ H) |
   generalize (Fcomp2_Lt _ _ H) |
   generalize (Fcomp2_Gt _ _ H) ] ;
 clear H ; intro H ; unfold float2R in * ; simpl in H ;
 rewrite mult_IZR in H.
rewrite <- H.
ring.
rewrite He.
apply Rmult_lt_compat_l with (1 := Hd) (2 := H).
unfold Rgt.
rewrite He.
apply Rmult_lt_compat_l with (1 := Hd) (2 := H).
rewrite Zpower_pos_nat.
induction (nat_of_P p).
apply refl_equal.
replace (Zpower_nat 5 (S n)) with (5 * Zpower_nat 5 n)%Z.
2: apply refl_equal.
rewrite mult_IZR.
rewrite IHn.
apply refl_equal.
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
intros x y.
unfold Dle_fd.
generalize (Dcompare_correct x y).
caseEq (Dcompare x y) ; intros ; auto with real.
discriminate.
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
intros x y.
unfold Dle_df.
generalize (Dcompare_correct y x).
caseEq (Dcompare y x) ; intros ; auto with real.
discriminate.
Qed.

End Gappa_decimal.
