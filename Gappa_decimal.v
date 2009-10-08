Require Import Gappa_common.
Require Import Gappa_integer.

Section Gappa_decimal.

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
change (Zpower_nat (Zpos x) (S n)) with ((Zpos x) * Zpower_nat (Zpos x) n)%Z.
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
intros x (ym, ye).
unfold Dcompare, float10R.
simpl.
induction ye.
(* ye = 0 *)
simpl.
change (Z2R ym) with (float2R (Float2 ym 0)).
case_eq (Fcomp2 x (Float2 ym 0)) ; intro H.
apply Fcomp2_Eq with (1 := H).
apply Fcomp2_Lt with (1 := H).
apply Fcomp2_Gt with (1 := H).
(* ye > 0 *)
assert (H0: (Float2 (ym * Zpower_pos 5 p) (Zpos p) = (Z2R ym * 10 ^ nat_of_P p)%R :>R)).
unfold float2R.
simpl.
do 2 rewrite mult_Z2R.
rewrite (Z2R_IZR (Zpower_pos 5 p)).
rewrite Zpower_pos_nat.
change 5%Z with (Z_of_nat 5).
rewrite Zpower_nat_powerRZ.
rewrite Zpower_pos_powerRZ.
rewrite Rmult_assoc.
unfold powerRZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite pow_exp.
replace (INR 5 * Z2R 2)%R with 10%R by (simpl ; ring).
apply refl_equal.
rewrite F2R_split.
case_eq (Fcomp2 x (Float2 (ym * Zpower_pos 5 p) (Zpos p))) ;
 intro H ;
 [ generalize (Fcomp2_Eq _ _ H) |
   generalize (Fcomp2_Lt _ _ H) |
   generalize (Fcomp2_Gt _ _ H) ] ;
 clear H ; rewrite H0 ; intro H ; exact H.
(* ye < 0 *)
rewrite F2R_split.
replace (P2R 10) with (IZR 5 * 2)%R by (simpl ; ring).
unfold powerRZ.
rewrite <- pow_exp.
rewrite Rinv_mult_distr ; try apply pow_nonzero.
2: apply not_O_IZR ; discriminate.
2: apply Rgt_not_eq ; exact (Z2R_lt 0 2 (refl_equal _)).
rewrite Rmult_comm.
rewrite Rmult_assoc.
cutrewrite (float2R x = (/ IZR 5 ^ nat_of_P p) * (x * (IZR 5 ^ nat_of_P p)))%R.
2: field ; apply pow_nonzero ; apply not_O_IZR ; discriminate.
cutrewrite (IZR 5 ^ nat_of_P p = IZR (Zpower_pos 5 p))%R.
rewrite <- (Rmult_comm (Z2R ym)).
assert (Hd: (0 < / Z2R (Zpower_pos 5 p))%R).
apply Rinv_0_lt_compat.
apply (Z2R_lt 0).
apply Zpower_pos_pos.
assert (He: (Z2R (Fnum x) * powerRZ 2 (Fexp x) * IZR (Zpower_pos 5 p)
 = Z2R (Fnum x) * IZR (Zpower_pos 5 p) * powerRZ 2 (Fexp x))%R) by ring.
unfold float2R.
rewrite F2R_split.
simpl (P2R 2).
rewrite He.
clear He.
rewrite <- Z2R_IZR.
rewrite <- mult_Z2R.
case_eq (Fcomp2 (Float2 (Fnum x * Zpower_pos 5 p) (Fexp x)) (Float2 ym (Zneg p))) ;
 intro H ;
 [ generalize (Fcomp2_Eq _ _ H) |
   generalize (Fcomp2_Lt _ _ H) |
   generalize (Fcomp2_Gt _ _ H) ] ;
 clear H ; intro H ; unfold float2R in * ;
 do 2 rewrite F2R_split in H ;
 simpl in H.
rewrite <- H.
apply refl_equal.
apply Rmult_lt_compat_l with (1 := Hd) (2 := H).
unfold Rgt.
apply Rmult_lt_compat_l with (1 := Hd) (2 := H).
rewrite Zpower_pos_nat.
induction (nat_of_P p).
apply refl_equal.
change (Zpower_nat 5 (S n)) with (5 * Zpower_nat 5 n)%Z.
rewrite mult_IZR.
rewrite <- IHn.
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
