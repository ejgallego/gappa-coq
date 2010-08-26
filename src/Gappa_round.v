Require Import Decidable.
Require Import Bool.
Require Import ZArith.
Require Import Reals.
Require Import Fcore_generic_fmt.
Require Import Fcalc_bracket.
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

Lemma round_rexp_exact :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 (rexp (e + Zpos (digits m)) <= e)%Z ->
 round_pos rdir rexp m e = (Npos m, e).
intros rdir rexp m e H.
unfold round_pos.
caseEq (rexp (e + Zpos (digits m)) - e)%Z ; intros ; try apply refl_equal.
elim H.
rewrite <- (Zcompare_plus_compat (rexp (e + Zpos (digits m))%Z) e (-e)).
rewrite Zplus_opp_l.
rewrite Zplus_comm.
unfold Zminus in H0.
rewrite H0.
apply refl_equal.
Qed.

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
  hrndG x e = Fcore_generic_fmt.Znearest (fun x => rdir (rnd_record_mk (ZtoN (Zfloor x)) true false) e) x.
Proof.
intros x e Hx1.
destruct (good_rdir (ZtoN (Zfloor x)) e) as (Hx2, _).
unfold hrndG, hrndG_aux.
destruct (inbetween_spec _ _ x (bracket_aux _)) as [Hx4|l Hx4 Hx5].
rewrite Hx2.
rewrite Hx4 at 2.
now rewrite Fcore_generic_fmt.Znearest_Z2R.
unfold Fcore_generic_fmt.Znearest.
rewrite Fcore_generic_fmt.Rcompare_floor_ceil_mid with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
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
now apply Fcore_generic_fmt.Znearest_monotone.
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
    rounding radix2 rexp ZhrndG (Fcore_defs.F2R (Fcore_defs.Float radix2 (Zpos m) e)).
Proof.
intros rexp m e.
assert (He: canonic_exponent radix2 rexp (Fcore_defs.F2R (Fcore_defs.Float radix2 (Zpos m) e)) = rexp (e + Zpos (digits m))%Z).
rewrite digits2_digits.
rewrite Fcalc_digits.digits_ln_beta. 2: easy.
unfold canonic_exponent.
rewrite Fcore_float_prop.ln_beta_F2R. 2: easy.
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
now apply (Fcore_float_prop.F2R_ge_0_compat radix2 (Fcore_defs.Float radix2 (Zpos m) (- (Zpos p)))).
intros _.
rewrite Z_of_N_ZtoN.
apply refl_equal.
apply Zfloor_lub.
now apply (Fcore_float_prop.F2R_ge_0_compat radix2 (Fcore_defs.Float radix2 (Zpos m) (- (Zpos p)))).
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
now rewrite Fcore_float_prop.F2R_0, rounding_0.
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
now apply Fcore_float_prop.F2R_gt_0_compat.
apply bpow_gt_0.
(* *)
unfold round. simpl.
change (Zneg m) with (- Zpos m)%Z.
rewrite <- Fcore_float_prop.opp_F2R.
generalize (hrndG_conversion (rneg rdir) (rneg_good _) rexp m e).
unfold rounding, ZrndG, rndG. simpl.
rewrite Rcompare_Lt.
rewrite canonic_exponent_opp.
rewrite scaled_mantissa_opp.
rewrite Ropp_involutive.
rewrite <- Fcore_float_prop.opp_F2R.
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
now apply Fcore_float_prop.F2R_gt_0_compat.
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

Lemma shr_constant_m :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 rnd_m (shr m2 (pos_of_Z (e1 - e2))) = (Npos m1).
intros m1 m2 e1 e2 H.
generalize (float2_repartition _ _ _ _ H).
intros (H1,H2).
cut (Z_of_N (rnd_m (shr m2 (pos_of_Z (e1 - e2)))) = Zpos m1).
intro H0.
unfold Z_of_N in H0.
destruct (rnd_m (shr m2 (pos_of_Z (e1 - e2)))).
discriminate H0.
injection H0. clear H0. intro H0. rewrite H0.
apply refl_equal.
apply dec_not_not.
apply dec_eq.
intro H0.
generalize (not_Zeq _ _ H0).
clear H0.
generalize (shr_bracket_weak (pos_of_Z (e1 - e2)) m2 e2).
rewrite (Zpos_pos_of_Z_minus _ _ H1).
cutrewrite (e2 + (e1 - e2) = e1)%Z. 2: ring.
simpl.
generalize (Z_of_N (rnd_m (shr m2 (pos_of_Z (e1 - e2))))).
intros m HH [H0|H0].
generalize (float2_binade_le _ _ e1 (Zlt_le_succ _ _ H0)).
apply Rlt_not_le.
apply Rlt_trans with (1 := proj1 H) (2 := proj2 HH).
generalize (float2_binade_le _ _ e1 (Zlt_le_succ _ _ H0)).
apply Rlt_not_le.
apply Rle_lt_trans with (1 := proj1 HH) (2 := proj2 H).
Qed.

Lemma shr_constant_m_underflow :
 forall m : positive, forall e k : Z,
 (Float2 (Zpos m) e < Float2 1 k)%R ->
 rnd_m (shr m (pos_of_Z (k - e))) = N0.
intros m e k H.
generalize (float2_repartition_underflow _ _ _ H).
intros H1.
assert (e < k)%Z.
generalize (Zgt_pos_0 (digits m)).
omega.
assert (Zpos (digits m) <= Z_of_nat (nat_of_P (pos_of_Z (k - e))))%Z.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite (Zpos_pos_of_Z_minus _ _ H0).
omega.
clear H1 H0 H.
unfold shr.
rewrite iter_nat_of_P.
generalize m H2. clear H2 m.
cut (forall m : positive, forall b1 b2 : bool,
  (Zpos (digits m) <= Z_of_nat (nat_of_P (pos_of_Z (k - e))))%Z ->
  rnd_m (iter_nat (nat_of_P (pos_of_Z (k - e))) rnd_record shr_aux
    (rnd_record_mk (Npos m) b1 b2)) = N0).
intros. apply H. exact H2.
induction (nat_of_P (pos_of_Z (k - e))) ; clear k e ; intros.
elim Zle_not_lt with (1 := H).
generalize (Zgt_pos_0 (digits m)).
simpl.
omega.
rewrite iter_nat_simpl.
simpl.
unfold shr_aux at 2.
simpl.
generalize H.
rewrite inj_S.
case m ; intros.
apply IHn.
simpl in H0.
rewrite Zpos_succ_morphism in H0.
unfold Zsucc in H0.
omega.
apply IHn.
simpl in H0.
rewrite Zpos_succ_morphism in H0.
unfold Zsucc in H0.
omega.
clear H0 H m IHn.
induction n ; intros.
apply refl_equal.
simpl.
unfold shr_aux at 1.
rewrite IHn.
apply refl_equal.
Qed.

Lemma shr_constant_s :
 forall d : positive,
 forall m1 : positive, forall e1 : Z,
 let m2 := (Z_of_N (rnd_m (shr m1 d)) * 2)%Z in
 let e2 := (e1 + Zpos d - 1)%Z in
 (Float2 (Zpos m1) e1 = Float2 m2 e2 :>R -> rnd_s (shr m1 d) = false) /\
 (Float2 (Zpos m1) e1 = Float2 (m2 + 1) e2 :>R -> rnd_s (shr m1 d) = false) /\
 (Float2 (Zpos m1) e1 <> Float2 m2 e2 :>R /\
  Float2 (Zpos m1) e1 <> Float2 (m2 + 1) e2 :>R -> rnd_s (shr m1 d) = true).
intros d m1 e1 m2 e2.
generalize (shr_bracket d m1 e1).
unfold bracket.
fold m2 e2.
caseEq (rnd_s (shr m1 d)) ; case (rnd_r (shr m1 d)) ;
intros Hs Hb ; split ; try split ; intros H ; try apply refl_equal.
elim Rlt_not_le with (1 := proj1 Hb).
rewrite H.
apply float2_binade_le.
auto with zarith.
elim Rlt_not_eq with (1 := proj1 Hb).
apply sym_eq with (1 := H).
elim Rlt_not_eq with (1 := proj1 Hb).
apply sym_eq with (1 := H).
elim Rlt_not_eq with (1 := proj2 Hb).
exact H.
elim (proj2 H).
exact Hb.
elim (proj1 H).
exact Hb.
Qed.

Lemma shr_constant_r :
 forall d : positive,
 forall m1 : positive, forall e1 : Z,
 let m2 := (Z_of_N (rnd_m (shr m1 d)) * 2)%Z in
 let e2 := (e1 + Zpos d - 1)%Z in
 ((Float2 m2 e2 <= Float2 (Zpos m1) e1 < Float2 (m2 + 1) e2)%R -> rnd_r (shr m1 d) = false) /\
 ((Float2 (m2 + 1) e2 <= Float2 (Zpos m1) e1 < Float2 (m2 + 2) e2)%R -> rnd_r (shr m1 d) = true).
intros d m1 e1 m2 e2.
generalize (shr_bracket d m1 e1).
unfold bracket.
fold m2 e2.
caseEq (rnd_r (shr m1 d)) ; case (rnd_s (shr m1 d)) ;
intros Hr Hb ; split ; intros H ; try apply refl_equal.
elim Rlt_not_le with (1 := proj2 H).
apply Rlt_le with (1 := proj1 Hb).
elim Rlt_not_eq with (1 := proj2 H).
exact Hb.
elim Rle_not_lt with (1 := proj1 H).
exact (proj2 Hb).
elim Rle_not_lt with (1 := proj1 H).
rewrite Hb.
apply float2_binade_lt.
auto with zarith.
Qed.

Lemma shr_constant_rs :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 let r := shr m2 (pos_of_Z (e1 - e2)) in
 ((Float2 (Zpos m2) e2 < Float2 (Zpos m1 * 2 + 1) (e1 - 1))%R -> rnd_r r = false /\ rnd_s r = true) /\
 (Float2 (Zpos m2) e2 = Float2 (Zpos m1 * 2 + 1) (e1 - 1) :>R -> rnd_r r = true /\ rnd_s r = false) /\
 ((Float2 (Zpos m1 * 2 + 1) (e1 - 1) < Float2 (Zpos m2) e2)%R -> rnd_r r = true /\ rnd_s r = true).
intros m1 m2 e1 e2 Hb.
generalize (shr_constant_m m1 m2 e1 e2 Hb).
intros Hm r.
generalize (shr_constant_r (pos_of_Z (e1 - e2)) m2 e2).
generalize (shr_constant_s (pos_of_Z (e1 - e2)) m2 e2).
rewrite Hm.
generalize (float2_repartition _ _ _ _ Hb).
intros (He,_).
rewrite (Zpos_pos_of_Z_minus _ _ He).
cutrewrite (e2 + (e1 - e2) - 1 = e1 - 1)%Z. 2: ring.
fold r.
intros (Hs1,(Hs2,Hs3)) (Hr1,Hr2).
split ; [ idtac | split ] ; intros H ; split.
apply Hr1.
split.
rewrite <- float2_shift_m1.
apply Rlt_le with (1 := proj1 Hb).
exact H.
apply Hs3.
split.
apply Rgt_not_eq.
rewrite <- float2_shift_m1.
exact (proj1 Hb).
apply Rlt_not_eq.
exact H.
apply Hr2.
split.
rewrite H.
apply Req_le.
apply refl_equal.
cutrewrite (Z_of_N (Npos m1) * 2 + 2 = (Z_of_N (Npos m1) + 1) * 2)%Z. 2: ring.
rewrite <- float2_shift_m1.
exact (proj2 Hb).
apply Hs2 with (1 := H).
apply Hr2.
split.
apply Rlt_le with (1 := H).
cutrewrite (Z_of_N (Npos m1) * 2 + 2 = (Z_of_N (Npos m1) + 1) * 2)%Z. 2: ring.
rewrite <- float2_shift_m1.
exact (proj2 Hb).
apply Hs3.
split.
apply Rgt_not_eq.
rewrite <- float2_shift_m1.
exact (proj1 Hb).
apply Rgt_not_eq.
exact H.
Qed.

Lemma rnd_record_eq :
 forall r : rnd_record,
 r = rnd_record_mk (rnd_m r) (rnd_r r) (rnd_s r).
induction r.
apply refl_equal.
Qed.

Lemma round_constant :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) = e1)%Z ->
 forall m2 : positive, forall e2 : Z,
 ((Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 * 2 + 1) (e1 - 1))%R
   -> round_pos rdir rexp m2 e2 = (if rdir (rnd_record_mk (Npos m1) false true) e1 then Nsucc (Npos m1) else Npos m1, e1)) /\
 (Float2 (Zpos m2) e2 = Float2 (Zpos m1 * 2 + 1) (e1 - 1) :>R
   -> round_pos rdir rexp m2 e2 = (if rdir (rnd_record_mk (Npos m1) true false) e1 then Nsucc (Npos m1) else Npos m1, e1)) /\
 ((Float2 (Zpos m1 * 2 + 1) (e1 - 1) < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R
   -> round_pos rdir rexp m2 e2 = (if rdir (rnd_record_mk (Npos m1) true true) e1 then Nsucc (Npos m1) else Npos m1, e1)).
intros rdir rexp m1 e1 Hf1 m2 e2.
split ; [ idtac | split ] ; intros Hf2.
assert (Hb: (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R).
split.
apply (proj1 Hf2).
apply Rlt_trans with (1 := proj2 Hf2).
rewrite (float2_shift_m1 e1).
apply float2_binade_lt.
auto with zarith.
generalize (float2_repartition m1 m2 e1 e2 Hb).
intros (H1,H2).
unfold round_pos.
rewrite <- H2.
rewrite Hf1.
rewrite <- (Zpos_pos_of_Z_minus _ _ H1).
pattern (shr m2 (pos_of_Z (e1 - e2))) at 1 ; rewrite rnd_record_eq.
rewrite (shr_constant_m m1 m2 e1 e2 Hb).
generalize (shr_constant_rs m1 m2 e1 e2 Hb).
intros (Hrs,_).
rewrite (proj1 (Hrs (proj2 Hf2))).
rewrite (proj2 (Hrs (proj2 Hf2))).
apply refl_equal.
assert (Hb: (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R).
rewrite Hf2.
repeat rewrite (float2_shift_m1 e1).
split.
apply float2_binade_lt.
auto with zarith.
apply float2_binade_lt.
auto with zarith.
generalize (float2_repartition m1 m2 e1 e2 Hb).
intros (H1,H2).
unfold round_pos.
rewrite <- H2.
rewrite Hf1.
rewrite <- (Zpos_pos_of_Z_minus _ _ H1).
pattern (shr m2 (pos_of_Z (e1 - e2))) at 1 ; rewrite rnd_record_eq.
rewrite (shr_constant_m m1 m2 e1 e2 Hb).
generalize (shr_constant_rs m1 m2 e1 e2 Hb).
intros (_,(Hrs,_)).
rewrite (proj1 (Hrs Hf2)).
rewrite (proj2 (Hrs Hf2)).
apply refl_equal.
assert (Hb: (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R).
split.
apply Rlt_trans with (2 := proj1 Hf2).
rewrite (float2_shift_m1 e1).
apply float2_binade_lt.
auto with zarith.
apply (proj2 Hf2).
generalize (float2_repartition m1 m2 e1 e2 Hb).
intros (H1,H2).
unfold round_pos.
rewrite <- H2.
rewrite Hf1.
rewrite <- (Zpos_pos_of_Z_minus _ _ H1).
pattern (shr m2 (pos_of_Z (e1 - e2))) at 1 ; rewrite rnd_record_eq.
rewrite (shr_constant_m m1 m2 e1 e2 Hb).
generalize (shr_constant_rs m1 m2 e1 e2 Hb).
intros (_,(_,Hrs)).
rewrite (proj1 (Hrs (proj1 Hf2))).
rewrite (proj2 (Hrs (proj1 Hf2))).
apply refl_equal.
Qed.

Lemma rexp_underflow :
 forall rexp : Z -> Z,
 good_rexp rexp ->
 forall k : Z,
 rexp k = k ->
 forall l : Z, (l <= k)%Z ->
 rexp l = k.
intros rexp Hg k Hk l Hl.
generalize (proj2 (Hg k)).
rewrite Hk.
intro H.
exact (proj2 (H (Zle_refl k)) l Hl).
Qed.

Lemma round_constant_underflow :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 good_rexp rexp ->
 forall e1 : Z, rexp e1 = e1 ->
 forall m2 : positive, forall e2 : Z,
 ((Float2 (Zpos m2) e2 < Float2 1 (e1 - 1))%R
   -> round_pos rdir rexp m2 e2 = (if rdir (rnd_record_mk N0 false true) e1 then (Npos xH) else N0, e1)) /\
 (Float2 (Zpos m2) e2 = Float2 1 (e1 - 1) :>R
   -> round_pos rdir rexp m2 e2 = (if rdir (rnd_record_mk N0 true false) e1 then (Npos xH) else N0, e1)) /\
 ((Float2 1 (e1 - 1) < Float2 (Zpos m2) e2 < Float2 1 e1)%R
   -> round_pos rdir rexp m2 e2 = (if rdir (rnd_record_mk N0 true true) e1 then (Npos xH) else N0, e1)).
intros rdir rexp Hge e1 Hf1 m2 e2.
generalize (rexp_underflow _ Hge _ Hf1 (e2 + Zpos (digits m2))).
split ; [ idtac | split ] ; intros Hf2.
assert (Hb: (Float2 (Zpos m2) e2 < Float2 1 e1)%R).
apply Rlt_trans with (1 := Hf2).
apply float2_Rlt_pow2.
omega.
generalize (float2_repartition_underflow _ _ _ Hb).
intro H0. generalize (H H0).
assert (e2 < rexp (e2 + Zpos (digits m2)))%Z.
generalize (Zgt_pos_0 (digits m2)).
omega.
clear H H0. intro H0.
unfold round_pos.
rewrite <- (Zpos_pos_of_Z_minus _ _ H1).
rewrite H0.
cutrewrite (shr m2 (pos_of_Z (e1 - e2)) = rnd_record_mk 0 false true).
apply refl_equal.
unfold shr.
rewrite iter_nat_of_P.
generalize (float2_repartition_underflow _ _ _ Hf2).
intros H.
rewrite H0 in H1.
clear H0 Hb Hf2 Hf1 Hge rexp rdir.
assert (Zpos (digits m2) <= Z_of_nat (nat_of_P (pos_of_Z (e1 - e2))) - 1)%Z.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite (Zpos_pos_of_Z_minus _ _ H1).
omega.
clear H1 H.
generalize m2 H0. clear H0 m2.
cut (forall m2 : positive, forall b1 b2 : bool,
  (Zpos (digits m2) <= Z_of_nat (nat_of_P (pos_of_Z (e1 - e2))) - 1)%Z ->
  iter_nat (nat_of_P (pos_of_Z (e1 - e2))) rnd_record shr_aux
    (rnd_record_mk (Npos m2) b1 b2) = rnd_record_mk 0 false true).
intros. apply H. exact H0.
induction (nat_of_P (pos_of_Z (e1 - e2))) ; clear e1 e2 ; intros.
elim Zle_not_lt with (1 := H).
generalize (Zgt_pos_0 (digits m2)).
simpl.
omega.
rewrite iter_nat_simpl.
simpl.
unfold shr_aux at 2.
simpl.
generalize H.
rewrite inj_S.
case m2 ; intros.
apply IHn.
simpl in H0.
rewrite Zpos_succ_morphism in H0.
unfold Zsucc in H0.
omega.
apply IHn.
simpl in H0.
rewrite Zpos_succ_morphism in H0.
unfold Zsucc in H0.
omega.
simpl in H0.
generalize H0.
case n ; intros.
compute in H1. elim H1.
apply refl_equal.
simpl.
clear H1.
induction n0.
apply refl_equal.
simpl.
rewrite IHn0.
apply refl_equal.
assert (Hb: (Float2 (Zpos m2) e2 < Float2 1 e1)%R).
rewrite Hf2.
apply float2_Rlt_pow2.
omega.
generalize (float2_repartition_underflow _ _ _ Hb).
intro H0. generalize (H H0). intro H1.
unfold round_pos.
caseEq (rexp (e2 + Zpos (digits m2)) - e2)%Z ; intros.
elim Zle_not_lt with (1 := H0).
generalize (Zgt_pos_0 (digits m2)).
omega.
rewrite H1.
cutrewrite (shr m2 p = rnd_record_mk 0 true false).
apply refl_equal.
rewrite H1 in H2.
assert (e2 <= e1 - 1)%Z. generalize (Zgt_pos_0 p). omega.
generalize (Zle_lt_or_eq _ _ H3).
clear H3. intros [H3|H3].
rewrite <- (float2_shl_correct 1 (e1 - 1)%Z (pos_of_Z (e1 - 1 - e2))) in Hf2.
simpl in Hf2.
cutrewrite (e1 - 1 - Zpos (pos_of_Z (e1 - 1 - e2)) = e2)%Z in Hf2.
2: rewrite (Zpos_pos_of_Z_minus _ _ H3) ; ring.
generalize (float2_binade_eq_reg _ _ _ Hf2).
intro H4. injection H4. intro H5. rewrite H5. clear H4 H5.
unfold shr.
rewrite iter_nat_of_P.
rewrite shift_pos_nat.
cutrewrite (nat_of_P p = S (nat_of_P (pos_of_Z (e1 - 1 - e2)))).
rewrite iter_nat_simpl.
simpl.
unfold shr_aux at 2, shift_nat.
simpl.
induction (nat_of_P (pos_of_Z (e1 - 1 - e2))).
exact (refl_equal _).
rewrite iter_nat_simpl.
simpl.
unfold shr_aux at 2. simpl.
exact IHn.
rewrite <- nat_of_P_succ_morphism.
cut (Zpos p = Zpos (Psucc (pos_of_Z (e1 - 1 - e2)))).
intros.
injection H4.
intros.
rewrite H5.
exact (refl_equal _).
rewrite <- H2.
rewrite Zpos_succ_morphism.
rewrite (Zpos_pos_of_Z_minus _ _ H3).
unfold Zsucc. ring.
assert (Zpos (digits m2) = 1%Z).
generalize (Zgt_pos_0 (digits m2)).
omega.
cutrewrite (m2 = xH).
cutrewrite (p = xH).
apply refl_equal.
cutrewrite (e1 - e2 = 1)%Z in H2.
apply sym_eq.
injection H2.
trivial.
rewrite H3.
ring.
injection H4.
clear H4 H3 H2 p H1 H0 Hb Hf2 H e2 Hf1 e1 Hge rexp rdir.
induction m2 ; simpl.
case (digits m2) ; intros ; discriminate.
case (digits m2) ; intros ; discriminate.
trivial.
elim Zle_not_lt with (1 := H0).
generalize (Zlt_neg_0 p).
generalize (Zgt_pos_0 (digits m2)).
omega.
rewrite (float2_shift_m1 e1) in Hf2.
cutrewrite (1 * 2 = 1 + 1)%Z in Hf2. 2: ring.
generalize (float2_repartition _ _ _ _ Hf2).
intros (H0,H1).
simpl in H1.
cutrewrite (e1 - 1 + 1 = e1)%Z in H1. 2: ring.
unfold round_pos.
rewrite <- H1 in H.
rewrite <- H1.
rewrite (H (Zle_refl e1)).
assert (e2 < e1)%Z. omega.
rewrite <- (Zpos_pos_of_Z_minus _ _ H2).
cutrewrite (shr m2 (pos_of_Z (e1 - e2)) = rnd_record_mk 0 true true).
exact (refl_equal _).
cutrewrite (pos_of_Z (e1 - e2) = 1 + pos_of_Z (e1 - 1 - e2))%positive.
unfold shr.
rewrite iter_pos_plus.
fold (shr m2 (pos_of_Z (e1 - 1 - e2))).
simpl.
unfold shr_aux.
rewrite (shr_constant_m _ _ _ _ Hf2).
generalize (shr_constant_rs _ _ _ _ Hf2).
simpl.
intros (H3,(H4,H5)).
case (Rtotal_order (Float2 (Zpos m2) e2) (Float2 3 (e1 - 1 - 1))) ;
[ intros H6 | intros [H6|H6] ].
rewrite (proj1 (H3 H6)).
rewrite (proj2 (H3 H6)).
apply refl_equal.
rewrite (proj1 (H4 H6)).
rewrite (proj2 (H4 H6)).
apply refl_equal.
unfold Rgt in H6.
rewrite (proj1 (H5 H6)).
rewrite (proj2 (H5 H6)).
apply refl_equal.
cut (Zpos (pos_of_Z (e1 - e2)) = Zpos (1 + pos_of_Z (e1 - 1 - e2))).
intros. injection H3. trivial.
rewrite (Zpos_pos_of_Z_minus _ _ H2).
rewrite <- Pplus_one_succ_l.
rewrite Zpos_succ_morphism.
rewrite (Zpos_pos_of_Z_minus _ _ H0).
unfold Zsucc.
ring.
Qed.

Lemma bracket_case :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 Float2 (Zpos m2) e2 = Float2 (Zpos m1) e1 :>R \/
 (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 * 2 + 1) (e1 - 1))%R \/
 Float2 (Zpos m2) e2 = Float2 (Zpos m1 * 2 + 1) (e1 - 1) :>R \/
 (Float2 (Zpos m1 * 2 + 1) (e1 - 1) < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R.
intros m1 m2 e1 e2 ([Hb1|Hb1],Hb2).
generalize (conj Hb1 Hb2).
clear Hb1 Hb2. intros Hb.
generalize (shr_bracket (pos_of_Z (e1 - e2)) m2 e2).
assert (e2 + Zpos (pos_of_Z (e1 - e2)) = e1)%Z.
rewrite Zpos_pos_of_Z_minus. ring.
exact (proj1 (float2_repartition _ _ _ _ Hb)).
rewrite H. clear H.
unfold bracket.
rewrite (shr_constant_m _ _ _ _ Hb).
unfold Z_of_N.
case (rnd_r (shr m2 (pos_of_Z (e1 - e2)))) ;
case (rnd_s (shr m2 (pos_of_Z (e1 - e2)))) ; intros H.
right. right. right.
split.
exact (proj1 H).
rewrite (float2_shift_m1 e1).
cutrewrite ((Zpos m1 + 1) * 2 = Zpos m1 * 2 + 2)%Z. 2 :ring.
exact (proj2 H).
right. right. left.
exact H.
right. left.
rewrite (float2_shift_m1 e1).
exact H.
left.
rewrite (float2_shift_m1 e1).
exact H.
left.
rewrite Hb1.
apply refl_equal.
Qed.

Lemma bracket_case_underflow :
 forall m : positive, forall e k : Z,
 (Float2 (Zpos m) e < Float2 1 k)%R ->
 (Float2 (Zpos m) e < Float2 1 (k - 1))%R \/
 Float2 (Zpos m) e = Float2 1 (k - 1) :>R \/
 (Float2 1 (k - 1) < Float2 (Zpos m) e < Float2 1 k)%R.
intros m e k Hb.
generalize (shr_bracket (pos_of_Z (k - e)) m e).
assert (e + Zpos (pos_of_Z (k - e)) = k)%Z.
rewrite Zpos_pos_of_Z_minus. ring.
generalize (float2_repartition_underflow _ _ _ Hb).
generalize (Zgt_pos_0 (digits m)).
omega.
rewrite H. clear H.
unfold bracket.
cutrewrite (rnd_m (shr m (pos_of_Z (k - e))) = N0 :>N).
simpl.
case (rnd_r (shr m (pos_of_Z (k - e)))) ;
case (rnd_s (shr m (pos_of_Z (k - e)))) ; intros H.
right. right.
split.
exact (proj1 H).
rewrite (float2_shift_m1 k).
exact (proj2 H).
right.  left.
exact H.
left.
exact (proj2 H).
left.
rewrite H.
apply float2_binade_lt.
exact (refl_equal Lt).
apply shr_constant_m_underflow.
exact Hb.
Qed.

Lemma rexp_case_aux :
 forall m1 : positive, forall e : Z,
 forall d : nat, d < nat_of_P (digits m1) ->
 exists m2 : positive,
 Npos m2 = match d with O => Npos m1 | S n => rnd_m (shr m1 (P_of_succ_nat n)) end /\
 (Float2 (Zpos m2) (e + Z_of_nat d) <= Float2 (Zpos m1) e < Float2 (Zpos m2 + 1) (e + Z_of_nat d))%R /\
 nat_of_P (digits m2) + d = nat_of_P (digits m1).
intros m1 e d Hd.
pose (m2 := iter_nat d positive (fun x => match x with xH => xH | xO p => p | xI p => p end) m1).
exists m2.
induction d.
rewrite Zplus_0_r.
simpl in m2.
unfold m2.
split. apply refl_equal.
split.
split. apply Rle_refl.
apply float2_binade_lt.
auto with zarith.
apply plus_0_r.
assert (d < nat_of_P (digits m1)).
omega.
generalize (IHd H). clear IHd.
rename m2 into m3.
set (m2 := iter_nat d positive (fun x : positive =>
  match x with xI p => p | xO p => p | xH => xH end) m1).
intros (H1,(H2,H3)).
split.
unfold m3.
unfold shr.
rewrite iter_nat_of_P.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
assert (Npos m2 = rnd_m (iter_nat d rnd_record shr_aux
  (rnd_record_mk (Npos m1) false false))).
rewrite H1.
case d.
apply refl_equal.
intro n.
unfold shr.
rewrite iter_nat_of_P.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
apply refl_equal.
clear H1.
simpl.
fold m2.
unfold shr_aux at 1.
rewrite <- H0.
caseEq m2 ; intros.
apply refl_equal.
apply refl_equal.
rewrite H1 in H3.
simpl in H3.
rewrite H3 in Hd.
elim (lt_irrefl _ Hd).
rewrite inj_S.
unfold Zsucc.
rewrite Zplus_assoc.
repeat rewrite float2_shift_p1.
assert (1 < nat_of_P (digits m2)). omega.
repeat rewrite <- (Zmult_comm 2).
unfold m3. simpl. fold m2.
split.
split.
apply Rle_trans with (2 := proj1 H2).
apply float2_binade_le.
caseEq m2 ; intros.
change (Zpos (xO p)) with (2 * Zpos p)%Z.
change (Zpos (xI p)) with (2 * Zpos p + 1)%Z.
auto with zarith.
apply Zle_refl.
rewrite H4 in H0.
unfold digits, nat_of_P in H0.
simpl in H0.
elim (lt_irrefl _ H0).
apply Rlt_le_trans with (1 := proj2 H2).
apply float2_binade_le.
caseEq m2 ; intros.
change (Zpos (xO (p + 1))) with (2 * (Zpos p + 1))%Z.
change (Zpos (xI p) + 1)%Z with (2 * Zpos p + 1 + 1)%Z.
auto with zarith.
change (Zpos (xO p) + 1)%Z with (2 * Zpos p + 1)%Z.
change (Zpos (xO (p + 1))) with (2 * (Zpos p + 1))%Z.
auto with zarith.
intros H5. discriminate.
rewrite <- plus_Snm_nSm.
rewrite <- H3.
repeat rewrite <- (plus_comm d).
apply (f_equal (plus d)).
caseEq m2 ; intros ; simpl ;
try (rewrite nat_of_P_succ_morphism ; apply refl_equal).
rewrite H4 in H0.
unfold digits, nat_of_P in H0.
simpl in H0.
elim (lt_irrefl _ H0).
Qed.

Lemma round_bound_local_strict :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) = e1)%Z ->
 forall m2 : positive, forall e2 : Z,
 (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 (Float2 (Zpos m1) e1 <= tofloat (round_pos rdir rexp m2 e2) <= Float2 (Zpos m1 + 1) e1)%R.
intros rdir rexp m1 e1 He m2 e2 (Hb1,Hb2).
assert (H0: forall b1 b2 : bool, (Float2 (Zpos m1) e1 <= tofloat
  (if rdir (rnd_record_mk (Npos m1) b1 b2) e1 then Nsucc (Npos m1)
  else Npos m1, e1) <= Float2 (Zpos m1 + 1) e1)%R).
intros b1 b2.
case (rdir (rnd_record_mk (Npos m1) b1 b2) e1).
simpl.
rewrite Zpos_succ_morphism.
split.
apply float2_binade_le.
exact (Zle_succ _).
apply Rle_refl.
simpl.
split.
apply Rle_refl.
apply float2_binade_le.
exact (Zle_succ _).
generalize (round_constant rdir rexp m1 e1 He m2 e2).
intros (Hc1,(Hc2,Hc3)).
generalize (bracket_case m1 m2 e1 e2 (conj (Rlt_le _ _ Hb1) Hb2)).
intros [H|[H|[H|H]]].
rewrite H in Hb1.
elim (Rlt_irrefl _ Hb1).
rewrite (Hc1 H).
apply H0.
rewrite (Hc2 H).
apply H0.
rewrite (Hc3 H).
apply H0.
Qed.

Lemma round_bound_local :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 good_rdir rdir ->
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) = e1)%Z ->
 forall m2 : positive, forall e2 : Z,
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 (Float2 (Zpos m1) e1 <= tofloat (round_pos rdir rexp m2 e2) <= Float2 (Zpos m1 + 1) e1)%R.
intros rdir rexp Hd m1 e1 He m2 e2 ([Hb1|Hb1],Hb2).
apply round_bound_local_strict with (1 := He) (2 := conj Hb1 Hb2).
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hd (sym_eq Hb1)).
unfold round_pos.
rewrite He.
rewrite Zminus_diag.
split.
apply Rle_refl.
simpl.
apply float2_binade_le.
exact (Zle_succ _).
Qed.

Lemma round_monotone :
  forall rdir : rnd_record -> Z -> bool,
  forall rexp : Z -> Z,
  good_rdir rdir ->
  good_rexp rexp ->
  forall m1 m2 : positive, forall e1 e2 : Z,
  (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2)%R ->
  (tofloat (round_pos rdir rexp m1 e1) <= tofloat (round_pos rdir rexp m2 e2))%R.
Proof.
intros rdir rexp Hdir Hexp m1 m2 e1 e2 H12.
rewrite 2!(hrndG_conversion _ Hdir).
apply rounding_monotone.
exact Hexp.
now rewrite <- 2!float2_float.
Qed.

Lemma log2 :
  forall x : R, (0 < x)%R ->
  { k : Z | (powerRZ 2 (k - 1) <= x < powerRZ 2 k)%R }.
Proof.
intros x Hx.
destruct (ln_beta radix2 x) as (e, H).
exists e.
specialize (H (Rgt_not_eq _ _ Hx)).
rewrite Rabs_right in H.
change 2%R with (Z2R (radix_val radix2)).
now rewrite <- 2!bpow_powerRZ.
apply Rle_ge.
now apply Rlt_le.
Qed.

Lemma rexp_case_real_aux :
 forall x : R, (0 < x)%R ->
 forall l k : Z, (k < l)%Z ->
 (powerRZ 2 (l - 1) <= x < powerRZ 2 l)%R ->
 (k + Zpos (digits (pos_of_Z (up (x * powerRZ 2 (-k)) - 1))) = l)%Z.
intros x Hp l k Hf Hx.
assert (powerRZ 2 (l - 1 - k) <= x * powerRZ 2 (-k) < powerRZ 2 (l - k))%R.
unfold Zminus at 1 3.
repeat (rewrite powerRZ_add ; [idtac | discrR]).
split.
apply Rmult_le_compat_r.
auto with real.
exact (proj1 Hx).
apply Rmult_lt_compat_r.
auto with real.
exact (proj2 Hx).
generalize (x * powerRZ 2 (-k))%R H.
clear Hx H.
intros r Hx.
cut (powerRZ 2 (l - 1 - k) <= Z2R (Zpos (pos_of_Z (up r - 1))) < powerRZ 2 (l - k))%R.
generalize (pos_of_Z (up r - 1)).
intros p H.
assert (Zpos (digits p) = l - k)%Z.
2: rewrite H0 ; ring.
apply Zle_antisym ; apply Znot_gt_le ; intro H0.
apply Rlt_not_le with (1 := proj2 H).
apply Rle_trans with (2 := proj1 (digits_correct p)).
assert (Float2 1 (l - k) <= Float2 1 (Zpos (digits p) - 1))%R.
apply float2_Rle_pow2.
omega.
unfold float2R in H1.
do 2 rewrite F2R_split in H1.
do 2 rewrite Rmult_1_l in H1.
exact H1.
apply Rle_not_lt with (1 := proj1 H).
apply Rlt_le_trans with (1 := proj2 (digits_correct p)).
assert (Float2 1 (Zpos (digits p)) <= Float2 1 (l - 1 - k))%R.
apply float2_Rle_pow2.
omega.
unfold float2R in H1.
do 2 rewrite F2R_split in H1.
do 2 rewrite Rmult_1_l in H1.
exact H1.
rewrite Zpos_pos_of_Z_minus.
unfold Zminus at 3 4.
rewrite plus_Z2R.
split.
cut (exists n : nat, (l - 1 - k = Z_of_nat n)%Z).
intros (n,H1).
generalize (proj1 Hx).
cutrewrite (powerRZ 2 (l - 1 - k) = IZR (Zpower_nat 2 n))%R.
intro H.
rewrite <- plus_Z2R.
rewrite Z2R_IZR.
apply IZR_le.
cut (Zpower_nat 2 n < up r)%Z.
omega.
apply lt_IZR.
apply Rle_lt_trans with (1 := H).
exact (proj1 (archimed _)).
change 2%Z with (Z_of_nat 2).
rewrite Zpower_nat_powerRZ.
rewrite H1.
apply refl_equal.
cut (0 <= l - 1 - k)%Z. 2: omega.
case (l - 1 - k)%Z ; intros.
exists 0. apply refl_equal.
exists (nat_of_P p). apply Zpos_eq_Z_of_nat_o_nat_of_P.
elim H.
apply refl_equal.
apply Rle_lt_trans with (2 := proj2 Hx).
apply Rplus_le_reg_l with (1 - r)%R.
simpl.
rewrite Z2R_IZR.
replace (1 - r + (IZR (up r) + -1))%R with (IZR (up r) - r)%R by ring.
replace (1 - r + r)%R with R1 by ring.
exact (proj2 (archimed _)).
apply lt_IZR.
apply Rle_lt_trans with (2 := proj1 (archimed r)).
apply Rle_trans with (2 := proj1 Hx).
assert (Float2 1 0 <= Float2 1 (l - 1 - k))%R.
apply float2_Rle_pow2.
omega.
unfold float2R in H.
do 2 rewrite F2R_split in H.
do 2 rewrite Rmult_1_l in H.
exact H.
Qed.

Lemma rexp_case_real :
 forall rexp : Z -> Z, good_rexp rexp ->
 forall x : R, (0 < x)%R ->
 { k : Z | rexp k = k /\ (x < Float2 1 k)%R } +
 { e : Z & { m : positive |
  rexp (e + Zpos (digits m))%Z = e /\
  (Float2 (Zpos m) e <= x < Float2 (Zpos m + 1) e)%R }}.
intros rexp Hg x Hx.
generalize (log2 x Hx).
intros (l, H).
case (Z_lt_le_dec (rexp l) l)%Z ; intro H0.
right.
exists (rexp l).
exists (pos_of_Z (up (x * powerRZ 2 (- rexp l)) - 1)).
split.
apply (f_equal rexp).
exact (rexp_case_real_aux _ Hx _ _ H0 H).
rewrite Zpos_pos_of_Z_minus.
unfold float2R. simpl.
split.
rewrite F2R_split.
apply Rle_trans with (((x * powerRZ 2 (- rexp l) + 1) - 1) * powerRZ 2 (rexp l))%R.
apply Rmult_le_compat_r.
auto with real.
rewrite minus_Z2R.
unfold Rminus. apply Rplus_le_compat_r.
replace (Z2R (up (x * powerRZ 2 (- rexp l)))) with (x * powerRZ 2 (- rexp l) +
  (Z2R (up (x * powerRZ 2 (- rexp l))) - x * powerRZ 2 (- rexp l)))%R by ring.
apply Rplus_le_compat_l.
rewrite Z2R_IZR.
exact (proj2 (archimed _)).
unfold Rminus. rewrite Rplus_assoc.
rewrite Rplus_opp_r. rewrite Rplus_0_r.
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
rewrite Zplus_opp_l.
auto with real.
unfold Zminus. rewrite <- Zplus_assoc.
rewrite Zplus_0_r.
apply Rle_lt_trans with (x * powerRZ 2 (- rexp l) * powerRZ 2 (rexp l))%R.
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
rewrite Zplus_opp_l.
auto with real.
rewrite F2R_split.
apply Rmult_lt_compat_r.
apply power_radix_pos.
rewrite Z2R_IZR.
exact (proj1 (archimed _)).
apply lt_IZR.
apply Rle_lt_trans with (2 := proj1 (archimed (x * powerRZ 2 (- rexp l)))).
apply Rle_trans with (x * powerRZ 2 (-l + 1))%R.
apply Rmult_le_reg_l with (powerRZ 2 (l - 1)).
auto with real.
rewrite Rmult_1_r.
rewrite (Rmult_comm x).
rewrite <- Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
replace (l - 1 + (- l + 1))%Z with Z0 by ring.
rewrite Rmult_1_l.
exact (proj1 H).
apply Rmult_le_compat_l.
exact (Rlt_le _ _ Hx).
assert (-l + 1 <= - rexp l)%Z.
omega.
generalize (float2_Rle_pow2 _ _ H1).
unfold float2R.
do 2 rewrite F2R_split.
do 2 rewrite Rmult_1_l.
intro H2. exact H2.
left.
exists (rexp l).
split.
apply (proj2 (proj2 (Hg l) H0)).
apply Zle_refl.
apply Rlt_le_trans with (1 := proj2 H).
cutrewrite (powerRZ 2 l = Float2 1 l).
apply float2_Rle_pow2 with (1 := H0).
unfold float2R.
rewrite F2R_split.
rewrite Rmult_1_l.
apply refl_equal.
Qed.

Lemma float2_density :
 forall x y : R, (0 < x < y)%R ->
 { e : Z & { m : positive |
 (x < Float2 (Zpos m) e < y)%R }}.
intros x y H.
generalize (log2 (y - x) (Rlt_Rminus _ _ (proj2 H))).
intros (k, H0).
exists (k - 2)%Z.
exists (pos_of_Z (up (x * powerRZ 2 (- (k - 2))))).
cutrewrite (Zpos (pos_of_Z (up (x * powerRZ 2 (- (k - 2))))) = up (x * powerRZ 2 (- (k - 2)))).
unfold float2R.
rewrite F2R_split.
simpl.
rewrite Z2R_IZR.
split.
pattern x at 1 ; replace x with (x * powerRZ 2 (- (k - 2)) * powerRZ 2 (k - 2))%R.
apply Rmult_lt_compat_r.
auto with real.
exact (proj1 (archimed _)).
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
replace (-(k - 2) + (k - 2))%Z with Z0 by ring.
apply Rmult_1_r.
apply Rle_lt_trans with ((x * powerRZ 2 (- (k - 2)) + 1) * powerRZ 2 (k - 2))%R.
apply Rmult_le_compat_r.
auto with real.
replace (IZR (up (x * powerRZ 2 (- (k - 2))))) with
  (x * powerRZ 2 (- (k - 2)) + (IZR (up (x * powerRZ 2 (- (k - 2))))
  - x * powerRZ 2 (- (k - 2))))%R by ring.
apply Rplus_le_compat_l.
exact (proj2 (archimed _)).
rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite <- powerRZ_add. 2: discrR.
cutrewrite (-(k - 2) + (k - 2) = 0)%Z. 2: ring.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
cutrewrite (y = x + (y - x))%R. 2: ring.
apply Rplus_lt_compat_l.
apply Rlt_le_trans with (2 := proj1 H0).
assert (k - 2 < k - 1)%Z. omega.
generalize (float2_Rlt_pow2 _ _ H1).
unfold float2R. simpl.
do 2 rewrite F2R_split.
do 2 rewrite Rmult_1_l.
intro H2. exact H2.
assert (0 < IZR (up (x * powerRZ 2 (- (k - 2)))))%R.
apply Rlt_trans with (x * powerRZ 2 (- (k - 2)))%R.
apply Rmult_lt_0_compat with (1 := proj1 H).
auto with real.
exact (proj1 (archimed _)).
change R0 with (IZR 0) in H1.
generalize (lt_IZR _ _ H1).
case (up (x * powerRZ 2 (- (k - 2)))) ; intros.
omega.
apply refl_equal.
generalize (Zlt_neg_0 p).
omega.
Qed.

Lemma round_density :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 good_rexp rexp ->
 forall x : R, (0 < x)%R ->
 { m1 : positive & { m2 : positive &
 { e1 : Z & { e2 : Z |
 let f1 := (Float2 (Zpos m1) e1) in
 let f2 := (Float2 (Zpos m2) e2) in
 (f1 <= x <= f2)%R /\
 round_pos rdir rexp m1 e1 = round_pos rdir rexp m2 e2 /\
 let e1' := snd (round_pos rdir rexp m1 e1) in rexp (e1 + Zpos (digits m1))%Z = e1' /\
 let e2' := snd (round_pos rdir rexp m2 e2) in rexp (e2 + Zpos (digits m2))%Z = e2' }}}}.
intros rdir rexp Hg x Hx.
generalize (rexp_case_real _ Hg _ Hx).
intros [(k,(Hk,Hx1))|(e,(m,(He,Hx1)))].
generalize (total_order_T x (Float2 1 (k - 1))).
intros [[Hx2|Hx2]|Hx2].
generalize (float2_density _ _ (conj Hx Hx2)).
intros (e2,(m2,(H2a,H2b))).
assert (0 < x * /2 < x)%R.
split.
apply Rmult_lt_0_compat with (1 := Hx).
auto with real.
pattern x at 2 ; rewrite <- Rmult_1_r.
pattern R1 at 3 ; rewrite <- Rinv_1.
auto with real.
generalize (float2_density _ _ H).
intros (e1,(m1,(_,H1b))).
clear H.
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ H1b).
exact (Rlt_le _ _ H2a).
generalize (round_constant_underflow rdir _ Hg _ Hk).
intros H.
assert (Float2 (Zpos m1) e1 < Float2 1 (k - 1))%R.
exact (Rlt_trans _ _ _ H1b Hx2).
rewrite (proj1 (H m1 e1) H0).
rewrite (proj1 (H m2 e2) H2b).
clear H H0.
simpl.
split.
apply refl_equal.
split ; apply rexp_underflow with (1 := Hg) (2 := Hk).
apply float2_repartition_underflow.
exact (Rlt_trans _ _ _ H1b Hx1).
apply float2_repartition_underflow.
apply Rlt_trans with (1 := H2b).
apply float2_Rlt_pow2.
omega.
exists xH. exists xH. exists (k - 1)%Z. exists (k - 1)%Z.
split.
rewrite Hx2.
split ; apply Rle_refl.
split.
apply refl_equal.
rewrite (proj1 (proj2 (round_constant_underflow rdir _ Hg _ Hk 1 (k - 1))) (refl_equal _)).
simpl.
cutrewrite (k - 1 + 1 = k)%Z. 2: ring.
exact (conj Hk Hk).
generalize (float2_density _ _ (conj Hx Hx1)).
intros (e2,(m2,H2)).
assert (0 < Float2 1 (k - 1))%R.
apply float2_pos_compat.
split.
generalize (float2_density _ _ (conj H Hx2)).
intros (e1,(m1,H1)).
clear H.
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ (proj2 H1)).
exact (Rlt_le _ _ (proj1 H2)).
generalize (round_constant_underflow rdir _ Hg _ Hk).
intros H.
assert (Float2 1 (k - 1) < Float2 (Zpos m1) e1 < Float2 1 k)%R.
split. exact (proj1 H1).
exact (Rlt_trans _ _ _ (proj2 H1) Hx1).
rewrite (proj2 (proj2 (H m1 e1)) H0).
clear H0.
assert (Float2 1 (k - 1) < Float2 (Zpos m2) e2 < Float2 1 k)%R.
split. 2: exact (proj2 H2).
exact (Rlt_trans _ _ _ Hx2 (proj1 H2)).
rewrite (proj2 (proj2 (H m2 e2)) H0).
clear H H0.
split.
apply refl_equal.
simpl.
split ; apply rexp_underflow with (1 := Hg) (2 := Hk).
apply float2_repartition_underflow.
exact (Rlt_trans _ _ _ (proj2 H1) Hx1).
apply float2_repartition_underflow.
exact (proj2 H2).
case (Rle_lt_or_eq_dec _ _ (proj1 Hx1)) ; intro Hx2.
generalize (conj Hx2 (proj2 Hx1)). clear Hx1 Hx2. intro Hx1.
generalize (total_order_T x (Float2 (Zpos m * 2 + 1) (e - 1))).
intros [[Hx2|Hx2]|Hx2].
assert (0 < Float2 (Zpos m) e)%R.
apply float2_pos_compat.
split.
generalize (float2_density _ _ (conj H (proj1 Hx1))).
intros (e1,(m1,(H1a,H1b))).
clear H.
generalize (float2_density _ _ (conj Hx Hx2)).
intros (e2,(m2,(H2a,H2b))).
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ H1b).
exact (Rlt_le _ _ H2a).
generalize (round_constant rdir rexp m e He).
intro H.
rewrite (proj1 (H m1 e1) (conj H1a (Rlt_trans _ _ _ H1b Hx2))).
rewrite (proj1 (H m2 e2) (conj (Rlt_trans _ _ _ (proj1 Hx1) H2a) H2b)).
clear H.
split.
apply refl_equal.
rewrite <- He.
simpl. split.
rewrite (proj2 (float2_repartition _ _ _ _ (conj H1a (Rlt_trans _ _ _ H1b (proj2 Hx1))))).
apply refl_equal.
assert (Float2 (Zpos m2) e2 < Float2 (Zpos m + 1) e)%R.
apply Rlt_trans with (1 := H2b).
rewrite (float2_shift_m1 e).
apply float2_binade_lt.
omega.
rewrite (proj2 (float2_repartition _ _ _ _ (conj (Rlt_trans _ _ _ (proj1 Hx1) H2a) H))).
apply refl_equal.
exists (xI m). exists (xI m). exists (e - 1)%Z. exists (e - 1)%Z.
split.
rewrite Hx2.
rewrite Zmult_comm.
split ; apply Rle_refl.
split.
apply refl_equal.
generalize (proj1 (proj2 (round_constant rdir rexp m e He (xI m) (e - 1)))).
cutrewrite (Zpos (xI m) = Zpos m * 2 + 1)%Z.
2: rewrite Zmult_comm ; apply refl_equal.
intro H. rewrite (H (refl_equal _)).
simpl.
rewrite Zpos_succ_morphism.
unfold Zsucc.
cutrewrite (e - 1 + (Zpos (digits m) + 1) = e + Zpos (digits m))%Z.
2: ring.
rewrite He.
split ; apply refl_equal.
assert (0 < Float2 (Zpos m * 2 + 1) (e - 1))%R.
apply float2_pos_compat.
split.
generalize (float2_density _ _ (conj H Hx2)).
intros (e1,(m1,(H1a,H1b))).
clear H.
generalize (float2_density _ _ (conj Hx (proj2 Hx1))).
intros (e2,(m2,(H2a,H2b))).
exists m1. exists m2. exists e1. exists e2.
split.
split.
exact (Rlt_le _ _ H1b).
exact (Rlt_le _ _ H2a).
generalize (round_constant rdir rexp m e He).
intro H.
rewrite (proj2 (proj2 (H m1 e1)) (conj H1a (Rlt_trans _ _ _ H1b (proj2 Hx1)))).
rewrite (proj2 (proj2 (H m2 e2)) (conj (Rlt_trans _ _ _ Hx2 H2a) H2b)).
clear H.
split.
apply refl_equal.
rewrite <- He.
simpl. split.
assert (Float2 (Zpos m) e < Float2 (Zpos m1) e1 < Float2 (Zpos m + 1) e)%R.
split.
apply Rlt_trans with (2 := H1a).
rewrite (float2_shift_m1 e).
apply float2_binade_lt.
omega.
exact (Rlt_trans _ _ _ H1b (proj2 Hx1)).
rewrite (proj2 (float2_repartition _ _ _ _ H)).
apply refl_equal.
rewrite (proj2 (float2_repartition _ _ _ _ (conj (Rlt_trans _ _ _ (proj1 Hx1) H2a) H2b))).
apply refl_equal.
exists m. exists m. exists e. exists e.
split.
rewrite Hx2.
split ; apply Rle_refl.
split.
apply refl_equal.
unfold round_pos.
rewrite He.
rewrite Zminus_diag.
split ; apply refl_equal.
Qed.

Lemma round_zero :
 forall rdir : round_dir,
 forall rexp : Z -> Z,
 forall e : Z,
 (round rdir rexp (Float2 Z0 e) = 0 :>R)%R.
intros rdir rexp e.
unfold round.
simpl.
apply float2_zero.
Qed.

Lemma round_extension :
 forall rdir : round_dir, forall rexp : Z -> Z,
 good_rexp rexp ->
 forall x : R, float2.
intros rdir rexp Hge x.
generalize (total_order_T 0 x).
intros [[Hx|Hx]|Hx].
generalize (round_density (rpos rdir) rexp Hge x Hx).
intros (m1,(m2,(e1,(e2,H)))).
exact (match round_pos (rpos rdir) rexp m1 e1 with (N0,_) => Float2 0 0 | (Npos m,e) => Float2 (Zpos m) e end).
exact (Float2 0 0).
assert (Hx': (0 < -x)%R). auto with real.
generalize (round_density (rneg rdir) rexp Hge (-x) Hx').
intros (m1,(m2,(e1,(e2,H)))).
exact (match round_pos (rneg rdir) rexp m1 e1 with (N0,_) => Float2 0 0 | (Npos m,e) => Float2 (Zneg m) e end).
Defined.

Lemma round_extension_prop_pos :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x : R, (0 < x)%R ->
 { m1 : positive & { m2 : positive &
 { e1 : Z & { e2 : Z |
 let f1 := (Float2 (Zpos m1) e1) in
 let f2 := (Float2 (Zpos m2) e2) in
 (f1 <= x <= f2)%R /\
 round_extension rdir rexp Hge x = round rdir rexp f1 /\
 round_extension rdir rexp Hge x = round rdir rexp f2 /\
 rexp (e1 + Zpos (digits m1))%Z = snd (round_pos (rpos rdir) rexp m1 e1) /\
 rexp (e2 + Zpos (digits m2))%Z = snd (round_pos (rpos rdir) rexp m2 e2) }}}}.
intros rdir rexp Hge x Hx.
unfold round_extension.
generalize (total_order_T 0 x).
intros [[H|H]|H].
generalize (round_density (rpos rdir) rexp Hge x H).
intros (m1,(m2,(e1,(e2,(H1,(H2,H3)))))).
exists m1. exists m2. exists e1. exists e2.
split. exact H1.
split. apply refl_equal.
split. rewrite H2. apply refl_equal.
exact H3.
rewrite H in Hx.
elim (Rlt_irrefl _ Hx).
elim (Rlt_irrefl _ (Rlt_trans _ _ _ Hx H)).
Qed.

Lemma round_extension_prop_neg :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge :good_rexp rexp,
 forall x : R, (0 > x)%R ->
 { m1 : positive & { m2 : positive &
 { e1 : Z & { e2 : Z |
 let f1 := (Float2 (Zpos m1) e1) in
 let f2 := (Float2 (Zpos m2) e2) in
 (f1 <= -x <= f2)%R /\
 let rdir' := round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir) in
 round_extension rdir rexp Hge x = Fopp2 (round rdir' rexp f1) /\
 round_extension rdir rexp Hge x = Fopp2 (round rdir' rexp f2) /\
 rexp (e1 + Zpos (digits m1))%Z = snd (round_pos (rneg rdir) rexp m1 e1) /\
 rexp (e2 + Zpos (digits m2))%Z = snd (round_pos (rneg rdir) rexp m2 e2) }}}}.
intros rdir rexp Hge x Hx.
unfold round_extension.
generalize (total_order_T 0 x).
intros [[H|H]|H].
elim (Rlt_irrefl _ (Rlt_trans _ _ _ Hx H)).
rewrite H in Hx.
elim (Rlt_irrefl _ Hx).
generalize (round_density (rneg rdir) rexp Hge (-x) (Ropp_0_gt_lt_contravar x H)).
intros (m1,(m2,(e1,(e2,(H1,(H2,H3)))))).
exists m1. exists m2. exists e1. exists e2.
split. exact H1.
split.
unfold round. simpl.
case (round_pos (rneg rdir) rexp m1 e1) ; intros.
case n ; intros ; apply refl_equal.
split.
unfold round. simpl.
rewrite H2.
case (round_pos (rneg rdir) rexp m2 e2) ; intros.
case n ; intros ; apply refl_equal.
exact H3.
Qed.

Lemma round_extension_conversion :
  forall rdir rexp (Hexp : good_rexp rexp) x,
  float2R (round_extension rdir rexp Hexp x) = rounding radix2 rexp (ZrndG rdir) x :>R.
Proof.
intros rdir rexp Hexp x.
unfold round_extension.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
(* *)
case round_density.
intros m1 (m2, (e1, (e2, (H1, (H2, H3))))).
replace (rounding radix2 rexp (ZrndG rdir) x) with (float2R (round rdir rexp (Float2 (Zpos m1) e1))).
apply refl_equal.
apply Rle_antisym.
rewrite rndG_conversion.
now apply rounding_monotone.
unfold round. simpl.
rewrite H2.
change (let (n, e) := round_pos (rpos rdir) rexp m2 e2 in match n with 0%N => Float2 0 0 | Npos q => Float2 (Zpos q) e end)
  with (round rdir rexp (Float2 (Zpos m2) e2)).
rewrite rndG_conversion.
now apply rounding_monotone.
(* *)
rewrite <- Hx.
rewrite rounding_0.
apply float2_zero.
(* *)
case round_density.
intros m1 (m2, (e1, (e2, (H1, (H2, H3))))).
replace (rounding radix2 rexp (ZrndG rdir) x) with (float2R (round rdir rexp (Float2 (- Zpos m1) e1))).
apply refl_equal.
apply Rle_antisym.
unfold round. simpl.
rewrite H2.
change (let (n, e) := round_pos (rneg rdir) rexp m2 e2 in match n with 0%N => Float2 0 0 | Npos q => Float2 (Zneg q) e end)
  with (round rdir rexp (Float2 (- Zpos m2) e2)).
rewrite rndG_conversion.
apply rounding_monotone.
exact Hexp.
apply Ropp_le_cancel.
now rewrite <- Fopp2_correct.
rewrite rndG_conversion.
apply rounding_monotone.
exact Hexp.
apply Ropp_le_cancel.
now rewrite <- Fopp2_correct.
Qed.

Lemma round_extension_float2 :
  forall rdir rexp (Hexp : good_rexp rexp) f,
  round_extension rdir rexp Hexp (float2R f) = round rdir rexp f :>R.
Proof.
intros rdir rexp Hexp f.
rewrite round_extension_conversion.
apply sym_eq.
apply rndG_conversion.
Qed.

Lemma round_extension_zero :
  forall rdir rexp (Hexp : good_rexp rexp),
  round_extension rdir rexp Hexp 0 = R0 :>R.
Proof.
intros rdir rexp Hexp.
rewrite round_extension_conversion.
apply rounding_0.
Qed.

Lemma round_extension_positive :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x : R, (0 < x)%R ->
 (0 <= round_extension rdir rexp Hge x)%R.
intros rdir rexp Hge x Hx.
generalize (round_extension_prop_pos rdir rexp Hge _ Hx).
intros (mx1,(mx2,(ex1,(ex2,(_,(Hx2,_)))))).
rewrite Hx2.
unfold round. simpl.
case (round_pos (rpos rdir) rexp mx1 ex1) ; intros.
case n ; intros.
apply Rle_refl.
apply Rlt_le.
apply float2_pos_compat.
split.
Qed.

Lemma round_extension_negative :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x : R, (0 > x)%R ->
 (round_extension rdir rexp Hge x <= 0)%R.
intros rdir rexp Hge x Hx.
generalize (round_extension_prop_neg rdir rexp Hge _ Hx).
intros (mx1,(mx2,(ex1,(ex2,(_,(Hx2,_)))))).
rewrite Hx2.
unfold round. simpl.
case (round_pos (rneg rdir) rexp mx1 ex1) ; intros.
destruct n.
apply Rle_refl.
apply Rge_le.
rewrite Fopp2_correct.
apply Ropp_0_le_ge_contravar.
apply Rlt_le.
apply float2_pos_compat.
split.
Qed.

Lemma round_extension_monotone :
  forall rdir rexp (Hexp : good_rexp rexp) x y,
  (x <= y)%R ->
  (round_extension rdir rexp Hexp x <= round_extension rdir rexp Hexp y)%R.
Proof.
intros rdir rexp Hexp x y Hxy.
rewrite 2!round_extension_conversion.
now apply rounding_monotone.
Qed.

Lemma round_extension_opp :
  forall rdir rexp (Hexp : good_rexp rexp) x,
  (round_extension rdir rexp Hexp (-x) = - round_extension
    (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir)) rexp Hexp x :>R)%R.
Proof.
intros rdir rexp Hexp x.
rewrite 2!round_extension_conversion.
rewrite rounding_opp.
apply f_equal.
apply rounding_ext.
clear x. intros x e.
unfold Zrounding_opp, Zrnd_opp, ZrndG, rndG. simpl.
destruct (Rcompare_spec x 0) as [H|H|H].
rewrite Rcompare_Gt.
apply refl_equal.
now apply Ropp_gt_lt_0_contravar.
rewrite H, Rcompare_Eq.
apply refl_equal.
apply Ropp_0.
rewrite Rcompare_Lt.
rewrite Ropp_involutive.
apply Zopp_involutive.
now apply Ropp_lt_gt_0_contravar.
Qed.

Definition rexp_representable (rexp : Z -> Z) (m e : Z) :=
 match m with
 | Z0 => True
 | Zpos p => (rexp (e + Zpos (digits p)) <= e)%Z
 | Zneg p => (rexp (e + Zpos (digits p)) <= e)%Z
 end.

Lemma round_extension_representable :
  forall rdir rexp (Hexp : good_rexp rexp) f,
  rexp_representable rexp (Fnum f) (Fexp f) ->
  round_extension rdir rexp Hexp f = f :>R.
Proof.
intros rdir rexp Hexp (m, e) H.
rewrite round_extension_conversion.
apply rounding_generic.
rewrite float2_float.
destruct m as [|m|m] ; simpl in H.
rewrite Fcore_float_prop.F2R_0.
apply generic_format_0.
apply generic_format_canonic_exponent.
unfold canonic_exponent.
rewrite Fcore_float_prop.ln_beta_F2R. 2: easy.
rewrite Zplus_comm.
rewrite <- Fcalc_digits.digits_ln_beta. 2: easy.
now rewrite <- digits2_digits.
change (Zneg m) with (- Zpos m)%Z.
rewrite <- Fcore_float_prop.opp_F2R.
apply generic_format_opp.
apply generic_format_canonic_exponent.
unfold canonic_exponent.
rewrite Fcore_float_prop.ln_beta_F2R. 2: easy.
rewrite Zplus_comm.
rewrite <- Fcalc_digits.digits_ln_beta. 2: easy.
now rewrite <- digits2_digits.
Qed.

Lemma representable_round_extension :
  forall rdir rexp (Hexp : good_rexp rexp) x,
  exists m : Z, exists e : Z,
  round_extension rdir rexp Hexp x = Float2 m e :>R /\ rexp_representable rexp m e.
Proof.
intros rdir rexp Hexp x.
rewrite round_extension_conversion.
rewrite generic_format_rounding with (1 := Hexp).
rewrite <- float2_float.
set (r := rounding radix2 rexp (ZrndG rdir) x).
eexists ; eexists ; repeat split.
unfold rexp_representable.
(* *)
assert (forall r p, generic_format radix2 rexp r -> Ztrunc (scaled_mantissa radix2 rexp r) = Zpos p ->
  (rexp (canonic_exponent radix2 rexp r + Zpos (digits p)) <= canonic_exponent radix2 rexp r)%Z).
clear r x.
intros x p Hx Hp.
rewrite digits2_digits.
rewrite Fcalc_digits.digits_ln_beta. 2: easy.
rewrite Zplus_comm.
rewrite <- Fcore_float_prop.ln_beta_F2R. 2: easy.
rewrite <- Hp.
rewrite <- Hx.
apply Zeq_le.
apply sym_eq.
destruct (ln_beta radix2 x) as (ex, He).
apply canonic_exponent_fexp.
apply He.
rewrite Hx.
apply Rgt_not_eq.
apply Fcore_float_prop.F2R_gt_0_compat.
now rewrite Hp.
(* *)
case_eq (Ztrunc (scaled_mantissa radix2 rexp r)) ; trivial ; intros p Hp.
apply H with (2 := Hp).
now apply generic_format_rounding.
rewrite <- canonic_exponent_opp.
apply H.
apply generic_format_opp.
now apply generic_format_rounding.
rewrite scaled_mantissa_opp.
rewrite Ztrunc_opp.
now rewrite Hp.
Qed.

End Gappa_round.
