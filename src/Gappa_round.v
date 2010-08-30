Require Import Decidable.
Require Import Bool.
Require Import ZArith.
Require Import Reals.
Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_integer.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.

Section Gappa_round.

Lemma iter_nat_simpl :
 forall n : nat, forall A : Set, forall f : A -> A, forall a : A,
 iter_nat (S n) A f a = iter_nat n A f (f a).
intros.
replace (S n) with (n + 1).
rewrite iter_nat_plus.
apply refl_equal.
rewrite plus_comm.
apply refl_equal.
Qed.

Definition shr_aux (p : rnd_record) : rnd_record :=
 let s := rnd_r p || rnd_s p in
 match (rnd_m p) with
 | N0 => rnd_record_mk N0 false s
 | Npos m1 =>
  match m1 with
  | xH => rnd_record_mk N0 true s
  | xO m2 => rnd_record_mk (Npos m2) false s
  | xI m2 => rnd_record_mk (Npos m2) true s
  end
 end.

Definition bracket (r : R) (p : rnd_record) (e : Z) :=
 let m := (Z_of_N (rnd_m p) * 2)%Z in
 let f0 := Float2 m (e - 1) in
 let f1 := Float2 (m + 1) (e - 1) in
 let f2 := Float2 (m + 2) (e - 1) in
 if (rnd_r p) then
  if (rnd_s p) then (f1 < r < f2)%R else (r = f1)%R
 else
  if (rnd_s p) then (f0 < r < f1)%R else (r = f0)%R.

Ltac caseEq f := generalize (refl_equal f) ; pattern f at -1 ; case f.

Lemma shr_aux_bracket :
 forall r : R, forall p : rnd_record, forall e : Z,
 bracket r p e -> bracket r (shr_aux p) (e + 1).
intros r p e H.
unfold bracket.
assert (H0: rnd_s (shr_aux p) = rnd_r p || rnd_s p).
unfold shr_aux.
destruct (rnd_m p) ; try destruct p0 ; trivial.
rewrite H0. clear H0.
assert (HH: if rnd_r p || rnd_s p then
              (Float2 (Z_of_N (rnd_m p)) (e + 1 - 1) < r < Float2 ((Z_of_N (rnd_m p) + 1)) (e + 1 - 1))%R
            else r = Float2 (Z_of_N (rnd_m p)) (e + 1 - 1)).
cutrewrite (e + 1 - 1 = e - 1 + 1)%Z. 2: ring.
repeat rewrite (float2_shift_p1).
cutrewrite ((Z_of_N (rnd_m p) + 1) * 2 = Z_of_N (rnd_m p) * 2 + 2)%Z.
2: ring.
unfold bracket in H.
destruct (rnd_r p) ; destruct (rnd_s p) ; simpl.
split. 2: apply (proj2 H).
apply Rlt_trans with (2 := proj1 H).
apply float2_binade_lt.
auto with zarith.
rewrite H.
split.
apply float2_binade_lt.
auto with zarith.
apply float2_binade_lt.
auto with zarith.
split. apply (proj1 H).
apply Rlt_trans with (1 := proj2 H).
apply float2_binade_lt.
auto with zarith.
exact H.
cutrewrite (Z_of_N (rnd_m (shr_aux p)) * 2 + 2 = Z_of_N (rnd_m (shr_aux p)) * 2 + 1 + 1)%Z.
2: ring.
caseEq (rnd_r (shr_aux p)) ; intro H0.
assert (Z_of_N (rnd_m (shr_aux p)) * 2 + 1 = Z_of_N (rnd_m p))%Z.
generalize H0. unfold shr_aux.
destruct (rnd_m p).
intros H1. discriminate H1.
destruct p0.
intros _. simpl. rewrite Pmult_comm. apply refl_equal.
intros H1. discriminate H1.
intros _. apply refl_equal.
rewrite H1.
exact HH.
assert (Z_of_N (rnd_m (shr_aux p)) * 2 = Z_of_N (rnd_m p))%Z.
generalize H0. unfold shr_aux.
destruct (rnd_m p).
intros _. apply refl_equal.
destruct p0.
intros H1. discriminate H1.
intros _. simpl. rewrite Pmult_comm. apply refl_equal.
intros H1. discriminate H1.
rewrite H1.
exact HH.
Qed.

Definition shr (m : positive) (d : positive) :=
 iter_pos d _ shr_aux (rnd_record_mk (Npos m) false false).

Lemma shr_bracket :
 forall d : positive,
 forall m : positive, forall e : Z,
 bracket (Float2 (Zpos m) e) (shr m d) (e + Zpos d).
intros d m e.
assert (bracket (Float2 (Zpos m) e) (rnd_record_mk (Npos m) false false) e).
unfold bracket.
simpl.
rewrite float2_shift_m1.
change (Zpos m * 2)%Z with (Zpos (m * 2)).
apply refl_equal.
unfold shr.
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P d).
rewrite iter_nat_of_P.
induction (nat_of_P d).
simpl.
rewrite Zplus_0_r.
exact H.
rewrite inj_S.
simpl.
unfold Zsucc. rewrite Zplus_assoc.
apply shr_aux_bracket with (1 := IHn).
Qed.

Lemma shr_bracket_weak :
 forall d : positive,
 forall m1 : positive, forall e1 : Z,
 let m2 := Z_of_N (rnd_m (shr m1 d)) in
 let e2 := (e1 + Zpos d)%Z in
 (Float2 m2 e2 <= Float2 (Zpos m1) e1 < Float2 (m2 + 1) e2)%R.
intros d m1 e1 m2 e2.
repeat rewrite (float2_shift_m1 e2).
generalize (shr_bracket d m1 e1).
unfold bracket.
case (rnd_r (shr m1 d)) ; case (rnd_s (shr m1 d)) ;
fold m2 ; fold e2 ; intro H.
split.
apply Rlt_le.
apply Rlt_trans with (2 := proj1 H).
apply float2_binade_lt.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H).
auto with zarith.
cutrewrite (m2 * 2 + 2 = (m2 + 1) * 2)%Z. 2: ring.
auto with real.
rewrite H.
split.
apply Rlt_le.
apply float2_binade_lt.
auto with zarith.
apply float2_binade_lt.
auto with zarith.
split.
apply Rlt_le.
apply (proj1 H).
apply Rlt_trans with (1 := proj2 H).
apply float2_binade_lt.
auto with zarith.
rewrite H.
split.
auto with real.
apply float2_binade_lt.
auto with zarith.
Qed.

Definition round_pos (rdir : rnd_record -> Z -> bool)
  (rexp : Z -> Z) (m : positive) (e : Z) :=
 let e' := rexp (e + Zpos (digits m))%Z in
 match (e' - e)%Z with
 | Zpos d =>
   let r := shr m d in
   ((if rdir r e' then Nsucc (rnd_m r) else rnd_m r), e')
 | _ => (Npos m, e)
 end.

Definition round (rdirs : round_dir) (rexp : Z -> Z) (f : float2) :=
 match (Fnum f) with
 | Z0 => Float2 Z0 Z0
 | Zpos p =>
   match (round_pos (rpos rdirs) rexp p (Fexp f)) with
   | (N0, _) => Float2 Z0 Z0
   | (Npos q, e) => Float2 (Zpos q) e
   end
 | Zneg p =>
   match (round_pos (rneg rdirs) rexp p (Fexp f)) with
   | (N0, _) => Float2 Z0 Z0
   | (Npos q, e) => Float2 (Zneg q) e
   end
 end.

Definition tofloat p := match p with
 | (m,e) => Float2 (Z_of_N m) e
 end.

Section ZrndG.

Section rndG.

Lemma bracket_aux :
  forall x,
  (Z2R (Zfloor x) <= x < Z2R (Zfloor x) + 1)%R.
Proof.
split.
apply Zfloor_lb.
apply Zfloor_ub.
Qed.

Variable rdir : rnd_record -> Z -> bool.
Variable good_rdir : good_rdir rdir.

Definition hrndG_aux mx x :=
  match inbetween_loc (Z2R mx) (Z2R mx + 1) x with
  | loc_Exact => (false, false)
  | loc_Inexact Lt => (false, true)
  | loc_Inexact Eq => (true, false)
  | loc_Inexact Gt => (true, true)
  end.

Definition hrndG x e :=
  let mx := Zfloor x in
  let m := ZtoN mx in
  let l := inbetween_loc (Z2R mx) (Z2R mx + 1) x in
  let r := let (r, s) := hrndG_aux mx x in rnd_record_mk m r s in
  if rdir r e then Zceil x else Zfloor x.

Lemma hrndG_DN :
  forall x e,
  rdir (rnd_record_mk (ZtoN (Zfloor x)) true true) e = false ->
  hrndG x e = Zfloor x.
Proof.
intros x e Hx1.
destruct (good_rdir (ZtoN (Zfloor x)) e) as (Hx2, (Hx3, Hx4)).
rewrite Hx1 in Hx4.
destruct Hx4 as [Hx4|Hx4] ; try easy.
rewrite Hx4 in Hx3.
destruct Hx3 as [Hx3|Hx3] ; try easy.
unfold hrndG.
destruct (hrndG_aux (Zfloor x) x) as ([|],[|]) ;
  now rewrite ?Hx1, ?Hx2, ?Hx3, ?Hx4.
Qed.

Lemma hrndG_UP :
  forall x e,
  rdir (rnd_record_mk (ZtoN (Zfloor x)) false true) e = true ->
  hrndG x e = Zceil x.
Proof.
intros x e Hx1.
destruct (good_rdir (ZtoN (Zfloor x)) e) as (Hx2, (Hx3, Hx4)).
rewrite Hx1 in Hx3.
destruct Hx3 as [Hx3|Hx3] ; try easy.
rewrite Hx3 in Hx4.
destruct Hx4 as [Hx4|Hx4] ; try easy.
unfold hrndG, hrndG_aux.
destruct (inbetween_spec _ _ x (bracket_aux _)) as [H|l H1 H2].
rewrite Hx2.
rewrite H at 2.
now rewrite Zceil_Z2R.
now case l ; rewrite ?Hx1, ?Hx3, ?Hx4.
Qed.

Lemma hrndG_N :
  forall x e,
  ( forall b, rdir (rnd_record_mk (ZtoN (Zfloor x)) b true) e = b ) ->
  hrndG x e = Znearest (fun x => rdir (rnd_record_mk (ZtoN (Zfloor x)) true false) e) x.
Proof.
intros x e Hx1.
destruct (good_rdir (ZtoN (Zfloor x)) e) as (Hx2, _).
unfold hrndG, hrndG_aux.
destruct (inbetween_spec _ _ x (bracket_aux _)) as [Hx4|l Hx4 Hx5].
rewrite Hx2.
rewrite Hx4 at 2.
now rewrite Znearest_Z2R.
unfold Znearest.
rewrite Rcompare_floor_ceil_mid with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
rewrite Rcompare_middle.
rewrite Zceil_floor_neq with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
rewrite plus_Z2R. simpl Z2R.
rewrite Hx5.
now case l ; rewrite ?Hx1, ?Hx2.
Qed.

Lemma hrndG_monotone :
  forall x y e, (x <= y)%R -> (hrndG x e <= hrndG y e)%Z.
Proof.
intros x y e Hxy.
destruct (Z_eq_dec (Zfloor x) (Zfloor y)) as [H|H].
(* *)
case_eq (rdir (rnd_record_mk (ZtoN (Zfloor x)) true true) e) ; intros Hb1.
case_eq (rdir (rnd_record_mk (ZtoN (Zfloor x)) false true) e) ; intros Hb2.
(* . *)
rewrite hrndG_UP with (1 := Hb2).
rewrite H in Hb2.
rewrite hrndG_UP with (1 := Hb2).
now apply Zceil_le.
(* . *)
assert (Hb3: forall b, rdir (rnd_record_mk (ZtoN (Zfloor x)) b true) e = b).
now intros [|].
rewrite hrndG_N with (1 := Hb3).
rewrite H in Hb3.
rewrite hrndG_N with (1 := Hb3).
now apply Znearest_monotone.
(* . *)
rewrite hrndG_DN with (1 := Hb1).
rewrite H in Hb1.
rewrite hrndG_DN with (1 := Hb1).
now apply Zfloor_le.
(* *)
apply Zle_trans with (Zceil x).
unfold hrndG.
case rdir.
apply Zle_refl.
apply le_Z2R.
exact (Rle_trans _ _ _ (Zfloor_lb x) (Zceil_ub x)).
apply Zle_trans with (Zfloor y).
apply Zle_trans with (Zfloor x + 1)%Z.
apply Zceil_glb.
rewrite plus_Z2R.
apply Rlt_le.
apply Zfloor_ub.
generalize (Zfloor_le x y Hxy).
omega.
unfold hrndG.
case rdir.
apply le_Z2R.
exact (Rle_trans _ _ _ (Zfloor_lb y) (Zceil_ub y)).
apply Zle_refl.
Qed.

Lemma hrndG_Z2R :
  forall n e, hrndG (Z2R n) e = n.
Proof.
intros n e.
unfold hrndG.
case rdir.
apply Zceil_Z2R.
apply Zfloor_Z2R.
Qed.

Lemma hrndG_pos :
  forall x e, (0 <= x)%R -> (0 <= hrndG x e)%Z.
Proof.
intros x e Hx.
rewrite <- (hrndG_Z2R 0 e).
now apply hrndG_monotone.
Qed.

Definition ZhrndG := mkZrounding hrndG hrndG_monotone hrndG_Z2R.

Lemma shr_conversion :
  forall m d,
  shr m d = let (r, s) := hrndG_aux (Zfloor (Z2R (Zpos m) * bpow radix2 (- Zpos d))) (Z2R (Zpos m) * bpow radix2 (- Zpos d)) in
    rnd_record_mk (ZtoN (Zfloor (Z2R (Zpos m) * bpow radix2 (- Zpos d)))) r s.
Proof.
intros m d.
unfold shr.
rewrite iter_nat_of_P.
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P d).
induction (nat_of_P d).
(* *)
simpl.
rewrite Rmult_1_r.
change (P2R m) with (Z2R (Zpos m)).
rewrite Zfloor_Z2R.
unfold hrndG_aux, inbetween_loc.
now rewrite Rcompare_Eq.
(* *)
simpl iter_nat.
rewrite IHn. clear IHn.
unfold hrndG_aux.
set (ms := (Z2R (Zpos m) * bpow radix2 (- Z_of_nat (S n)))%R).
replace (Z2R (Zpos m) * bpow radix2 (- Z_of_nat n))%R with (ms * 2)%R.
assert (H0: (0 <= Zfloor ms)%Z).
apply Zfloor_lub.
unfold ms.
apply Rmult_le_pos.
now apply (Z2R_le 0).
apply bpow_ge_0.
clearbody ms. clear -H0.
destruct (inbetween_spec _ _ ms (bracket_aux _)) as [H|l H1 H2].
(* . *)
replace (Zfloor (ms * 2)) with (Zfloor ms * 2)%Z.
unfold inbetween_loc.
rewrite mult_Z2R.
rewrite Rcompare_Eq.
destruct (Zfloor ms) as [|p|p] ; try easy.
now rewrite Zmult_comm.
now rewrite <- H.
rewrite H at 2.
change 2%R with (Z2R 2).
rewrite <- mult_Z2R.
now rewrite Zfloor_Z2R.
(* . *)
unfold inbetween_loc.
assert (H3: Rcompare (ms * 2) (Z2R (Zfloor ms) * 2 + 1) = l).
rewrite <- (Rcompare_mult_r 2) in H2.
now replace (Z2R (Zfloor ms) * 2 + 1)%R with ((Z2R (Zfloor ms) + (Z2R (Zfloor ms) + 1)) / 2 * 2)%R by field.
now apply (Z2R_lt 0 2).
clear H2. rewrite <- H3. clear H3.
case Rcompare_spec ; intros H4.
elim Rlt_not_le with (1 := H4).
apply Zfloor_lb.
(* .. *)
unfold shr_aux. simpl.
rewrite H4.
change (Z2R (Zfloor ms) * 2 + 1)%R with (Z2R (Zfloor ms) * Z2R 2 + Z2R 1)%R.
rewrite <- mult_Z2R, <- plus_Z2R.
rewrite Rcompare_Z2R.
rewrite <- H4.
replace (Zfloor (ms * 2)) with (1 + 2 * Zfloor ms)%Z.
rewrite Zcompare_Eq.
clear -H0.
destruct (Zfloor ms) as [|p|p] ; try easy.
now elim H0.
now rewrite Zmult_comm, Zplus_comm.
clear -H1 H4.
assert (Zfloor ms * 2 < Zfloor (ms * 2) < (Zfloor ms + 1) * 2)%Z.
split ; apply lt_Z2R ; rewrite <- H4 ; rewrite mult_Z2R ; apply Rmult_lt_compat_r.
now apply (Z2R_lt 0 2).
apply H1.
now apply (Z2R_lt 0 2).
now rewrite plus_Z2R.
omega.
(* .. *)
set (rs := match Rcompare (ms * 2) ((Z2R (Zfloor (ms * 2)) + (Z2R (Zfloor (ms * 2)) + 1)) / 2) with
  Eq => (true, false) | Lt => (false, true) | Gt => (true, true) end).
rewrite (surjective_pairing rs).
unfold shr_aux. simpl.
replace (fst rs || snd rs) with true.
clear rs.
case Rcompare_spec ; intros H2.
(* ... *)
replace (Zfloor (ms * 2)) with (2 * Zfloor ms)%Z.
now case (Zfloor ms).
apply sym_eq.
rewrite Zmult_comm.
apply Zfloor_imp.
rewrite plus_Z2R, mult_Z2R.
refine (conj _ H2).
apply Rmult_le_compat_r.
now apply (Z2R_le 0 2).
apply Zfloor_lb.
(* ... *)
elim Rlt_not_le with (1 := H4).
rewrite H2.
change (Z2R (Zfloor ms) * 2 + 1)%R with (Z2R (Zfloor ms) * Z2R 2 + Z2R 1)%R.
rewrite <- mult_Z2R, <- plus_Z2R.
rewrite Zfloor_Z2R.
apply Rle_refl.
(* ... *)
replace (Zfloor (ms * 2)) with (1 + 2 * Zfloor ms)%Z.
revert H0.
case (Zfloor ms) ; try easy.
intros p H. now elim H.
apply sym_eq.
apply Zfloor_imp.
rewrite plus_Z2R, mult_Z2R.
split.
rewrite Rplus_comm, Rmult_comm.
now apply Rlt_le.
rewrite 2!plus_Z2R, mult_Z2R.
simpl.
replace (1 + 2 * Z2R (Zfloor ms) + 1)%R with ((Z2R (Zfloor ms) + 1) * 2)%R by ring.
apply Rmult_lt_compat_r.
now apply (Z2R_lt 0 2).
apply H1.
(* ... *)
unfold rs.
now case Rcompare.
unfold ms.
rewrite Rmult_assoc.
change 2%R with (bpow radix2 1).
rewrite <- bpow_add.
apply (f_equal (fun e => _ * bpow radix2 e)%R).
rewrite inj_S.
unfold Zsucc.
ring.
Qed.

Lemma Z_of_N_ZtoN :
  forall n, (0 <= n)%Z -> Z_of_N (ZtoN n) = n.
Proof.
intros [|p|p] H ; try easy.
now elim H.
Qed.

Theorem hrndG_conversion :
  forall rexp m e,
  float2R (tofloat (round_pos rdir rexp m e)) =
    rounding radix2 rexp ZhrndG (Fcore_defs.F2R (Float radix2 (Zpos m) e)).
Proof.
intros rexp m e.
assert (He: canonic_exponent radix2 rexp (Fcore_defs.F2R (Float radix2 (Zpos m) e)) = rexp (e + Zpos (digits m))%Z).
rewrite digits2_digits.
rewrite digits_ln_beta. 2: easy.
unfold canonic_exponent.
rewrite ln_beta_F2R. 2: easy.
now rewrite Zplus_comm.
unfold round_pos.
case_eq (rexp (e + Zpos (digits m)) - e)%Z.
(* *)
intros H.
rewrite rounding_generic.
unfold Fcore_defs.F2R, float2R.
simpl.
rewrite F2R_split.
now rewrite bpow_powerRZ.
apply generic_format_canonic_exponent.
rewrite He.
rewrite Zminus_eq with (1 := H).
apply Zle_refl.
(* *)
intros p H.
unfold rounding, scaled_mantissa.
rewrite He.
unfold Fcore_defs.F2R, float2R.
rewrite Rmult_assoc, <- bpow_add.
simpl.
assert (rexp (e + Zpos (digits m)) = e + Zpos p)%Z.
omega.
rewrite H0.
ring_simplify (e + -(e + Zpos p))%Z.
rewrite F2R_split.
rewrite (bpow_powerRZ radix2 (e + Zpos p)).
apply (f_equal (fun m => Z2R m * _)%R).
unfold hrndG.
rewrite (shr_conversion m p).
simpl.
set (rs := hrndG_aux (Zfloor (P2R m * / Z2R (Zpower_pos 2 p))) (P2R m * / Z2R (Zpower_pos 2 p))).
rewrite (surjective_pairing rs).
simpl.
assert (H1: rdir(rnd_record_mk (ZtoN (Zfloor (P2R m * / Z2R (Zpower_pos 2 p)))) (fst rs) (snd rs)) (e + Zpos p) = true ->
  (Z2R (Zfloor (P2R m * / Z2R (Zpower_pos 2 p))) <> P2R m * / Z2R (Zpower_pos 2 p))%R).
unfold rs, hrndG_aux.
destruct (inbetween_spec _ _ (P2R m * / Z2R (Zpower_pos 2 p)) (bracket_aux _)) as [H1|l H1 H2].
simpl.
intros H2 _.
destruct (good_rdir (ZtoN (Zfloor (P2R m * / Z2R (Zpower_pos 2 p)))) (e + Zpos p)%Z) as (H3, _).
now rewrite H2 in H3.
intros _.
now apply Rlt_not_eq.
revert H1.
case rdir.
intros H1.
rewrite Nnat.Z_of_N_succ.
rewrite Z_of_N_ZtoN.
apply sym_eq.
apply Zceil_floor_neq.
now apply H1.
apply Zfloor_lub.
now apply (F2R_ge_0_compat radix2 (Float radix2 (Zpos m) (- (Zpos p)))).
intros _.
rewrite Z_of_N_ZtoN.
apply refl_equal.
apply Zfloor_lub.
now apply (F2R_ge_0_compat radix2 (Float radix2 (Zpos m) (- (Zpos p)))).
(* *)
intros p H.
rewrite rounding_generic.
unfold Fcore_defs.F2R, float2R.
simpl.
rewrite F2R_split.
now rewrite bpow_powerRZ.
apply generic_format_canonic_exponent.
rewrite He.
generalize (Zlt_neg_0 p).
omega.
Qed.

End rndG.

Variable rdir : round_dir.

Definition rndG x e:=
  match Rcompare x 0 with
  | Gt => hrndG (rpos rdir) x e
  | Lt => Zopp (hrndG (rneg rdir) (-x) e)
  | _ => Z0
  end.

Lemma rndG_monotone :
  forall x y e, (x <= y)%R -> (rndG x e <= rndG y e)%Z.
Proof.
intros x y e Hxy.
unfold rndG.
destruct (Rcompare_spec x 0) as [Hx|Hx|Hx].
(* *)
destruct (Rcompare_spec y 0) as [Hy|Hy|Hy].
(* . *)
apply Zopp_le_cancel.
rewrite 2!Zopp_involutive.
apply hrndG_monotone.
apply rneg_good.
now apply Ropp_le_contravar.
(* . *)
apply Zopp_le_cancel.
rewrite Zopp_involutive.
apply hrndG_pos.
apply rneg_good.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
(* . *)
apply Zle_trans with Z0.
apply Zopp_le_cancel.
rewrite Zopp_involutive.
apply hrndG_pos.
apply rneg_good.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
apply hrndG_pos.
apply rpos_good.
now apply Rlt_le.
(* *)
destruct (Rcompare_spec y 0) as [Hy|Hy|Hy].
elim Rle_not_lt with (1 := Hxy).
now rewrite Hx.
apply Zle_refl.
apply hrndG_pos.
apply rpos_good.
now apply Rlt_le.
(* *)
rewrite Rcompare_Gt.
apply hrndG_monotone.
apply rpos_good.
exact Hxy.
now apply Rlt_le_trans with x.
Qed.

Lemma rndG_Z2R :
  forall n e, rndG (Z2R n) e = n.
Proof.
intros n e.
unfold rndG.
change R0 with (Z2R 0).
rewrite Rcompare_Z2R.
rewrite <- opp_Z2R.
rewrite 2!hrndG_Z2R.
rewrite Zopp_involutive.
now case n.
Qed.

Definition ZrndG := mkZrounding rndG rndG_monotone rndG_Z2R.

Theorem rndG_conversion :
  forall rexp f,
  float2R (round rdir rexp f) = rounding radix2 rexp ZrndG (float2R f).
Proof.
intros rexp (m, e).
rewrite float2_float.
destruct m as [|m|m].
now rewrite F2R_0, rounding_0.
(* *)
unfold round. simpl.
generalize (hrndG_conversion (rpos rdir) (rpos_good _) rexp m e).
unfold rounding, ZrndG, rndG. simpl.
rewrite Rcompare_Gt.
intros H.
rewrite <- H.
case round_pos.
intros [|n] z ; simpl.
now rewrite 2!float2_zero.
apply refl_equal.
unfold scaled_mantissa.
apply Rmult_lt_0_compat.
now apply F2R_gt_0_compat.
apply bpow_gt_0.
(* *)
unfold round. simpl.
change (Zneg m) with (- Zpos m)%Z.
rewrite <- opp_F2R.
generalize (hrndG_conversion (rneg rdir) (rneg_good _) rexp m e).
unfold rounding, ZrndG, rndG. simpl.
rewrite Rcompare_Lt.
rewrite canonic_exponent_opp.
rewrite scaled_mantissa_opp.
rewrite Ropp_involutive.
rewrite <- opp_F2R.
intros H.
rewrite <- H.
case round_pos.
intros [|n] z ; simpl.
rewrite 2!float2_zero.
now rewrite Ropp_0.
now rewrite <- Fopp2_correct.
rewrite scaled_mantissa_opp.
apply Ropp_lt_gt_0_contravar.
unfold scaled_mantissa.
apply Rmult_lt_0_compat.
now apply F2R_gt_0_compat.
apply bpow_gt_0.
Qed.

End ZrndG.

Lemma roundDN_DN :
  forall x e,
  Zrnd (ZrndG roundDN) x e = Zfloor x.
Proof.
intros x e.
simpl.
unfold rndG.
case Rcompare_spec ; intros H.
rewrite hrndG_UP.
unfold Zceil.
rewrite Ropp_involutive.
apply Zopp_involutive.
apply roundDN.
apply refl_equal.
rewrite H.
apply sym_eq.
exact (Zfloor_Z2R 0).
rewrite hrndG_DN ; try easy.
apply roundDN.
Qed.

Lemma roundNE_NE :
  forall x e,
  Zrnd (ZrndG roundNE) x e = Znearest (fun m => negb (Zeven (Zfloor x))) x.
Proof.
intros x e.
simpl.
destruct (Req_dec (Z2R (Zfloor x)) x) as [H1|H1].
rewrite <- H1.
now rewrite rndG_Z2R, Znearest_Z2R.
unfold rndG.
case Rcompare_spec ; intros H2.
(* *)
rewrite hrndG_N.
unfold Znearest. simpl.
replace (-x - Z2R (Zfloor (-x)))%R with (Z2R (Zceil x) - x)%R.
rewrite Rcompare_floor_ceil_mid with (1 := H1).
rewrite Rcompare_ceil_floor_mid with (1 := H1).
rewrite Rcompare_sym.
case Rcompare ; simpl.
unfold rndNE. simpl.
rewrite <- (Zopp_involutive (Zfloor (-x))).
fold (Zceil x).
rewrite Zceil_floor_neq with (1 := H1).
unfold Zceil.
rewrite Ropp_involutive.
assert (H3: (Zfloor x < 0)%Z).
generalize (Zceil_floor_neq _ H1).
generalize (Zceil_glb 0 _ (Rlt_le _ _ H2)).
omega.
clear -H3.
now destruct (Zfloor x) as [|p|[p|[p|p|]|]].
unfold Zceil.
rewrite Ropp_involutive.
apply Zopp_involutive.
apply refl_equal.
unfold Zceil.
rewrite opp_Z2R.
apply Rplus_comm.
apply roundNE.
exact andb_true_r.
(* *)
rewrite H2.
apply sym_eq.
exact (Znearest_Z2R _ 0).
(* *)
rewrite hrndG_N.
unfold Znearest. simpl.
case Rcompare ; try apply refl_equal.
unfold rndNE. simpl.
assert (H3: (0 <= Zfloor x)%Z).
apply Zfloor_lub.
now apply Rlt_le.
clear -H3.
destruct (Zfloor x) as [|p|p] ; try easy.
now elim H3.
apply roundNE.
exact andb_true_r.
Qed.

Lemma tofloat_pair :
 forall p : N * Z,
 tofloat p = Float2 (Z_of_N (fst p)) (snd p).
intros (n,e).
exact (refl_equal _).
Qed.

Lemma tofloat_0 :
 forall p,
 float2R (match p with (N0,_) => Float2 0 0 | (Npos p, e) => Float2 (Zpos p) e end) = tofloat p.
intros (n,e).
case n.
unfold tofloat.
repeat rewrite float2_zero.
exact (refl_equal _).
intros.
exact (refl_equal _).
Qed.

Lemma round_unicity :
  forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
  forall m1 m2 : positive, forall e1 e2 : Z,
  good_rdir rdir ->
  Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R ->
  tofloat (round_pos rdir rexp m1 e1) = tofloat (round_pos rdir rexp m2 e2) :>R.
Proof.
intros rdir rexp m1 m2 e1 e2 Hdir Heq.
rewrite 2!(hrndG_conversion _ Hdir).
rewrite <- 2!float2_float.
now apply f_equal.
Qed.

Definition good_rexp (rexp : Z -> Z) :=
 forall k : Z,
 ((rexp k < k)%Z -> (rexp (k + 1) <= k)%Z) /\
 ((k <= rexp k)%Z -> (rexp (rexp k + 1) <= rexp k)%Z /\
                     forall l : Z, (l <= rexp k)%Z -> rexp l = rexp k).

Lemma rexp_succ :
 forall rexp : Z -> Z,
 good_rexp rexp ->
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) <= e1)%Z ->
 exists m2 : positive, exists e2 : Z,
 Float2 (Zpos m2) e2 = Float2 (Zpos m1 + 1) e1 :>R /\
 (rexp (e2 + Zpos (digits m2)) <= e2)%Z.
intros rexp He m1 e1 He1.
cut (digits (Psucc m1) = digits m1 \/
     Psucc m1 = iter_pos (digits m1) positive xO xH).
intros [H|H].
exists (Psucc m1). exists e1.
rewrite Zpos_succ_morphism.
rewrite H.
split.
apply refl_equal.
exact He1.
exists xH.
exists (e1 + Zpos (digits m1))%Z.
cutrewrite (Zpos m1 + 1 = Zpos (Psucc m1))%Z.
rewrite H.
simpl.
split.
clear He He1 H.
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P (digits m1)).
rewrite iter_nat_of_P.
induction (nat_of_P (digits m1)).
rewrite Zplus_0_r.
apply refl_equal.
rewrite inj_S.
simpl.
unfold float2R in *.
repeat rewrite F2R_split in *.
rewrite Rmult_1_l in *.
rewrite Z2R_IZR.
simpl in *.
rewrite nat_of_P_xO.
rewrite mult_INR.
rewrite Rmult_assoc.
rewrite <- P2R_INR.
rewrite <- IHn.
unfold Zsucc.
rewrite Zplus_assoc.
rewrite powerRZ_add. 2: discrR.
simpl.
ring.
assert (rexp (e1 + Zpos (digits m1)) < e1 + Zpos (digits m1))%Z.
apply Zle_lt_trans with (1 := He1).
generalize (Zgt_pos_0 (digits m1)).
omega.
exact (proj1 (He (e1 + Zpos (digits m1))%Z) H0).
rewrite Zpos_succ_morphism.
apply refl_equal.
clear He rexp He1 e1.
induction m1.
elim IHm1 ; intro H ; clear IHm1 ; [ left | right ].
simpl.
rewrite H.
apply refl_equal.
rewrite iter_nat_of_P.
simpl.
rewrite nat_of_P_succ_morphism.
simpl.
rewrite <- iter_nat_of_P.
rewrite H.
apply refl_equal.
left.
apply refl_equal.
right.
apply refl_equal.
Qed.

End Gappa_round.
