Require Import Decidable.
Require Import Bool.
Require Import ZArith.
Require Import Reals.
Require Import Fcore.
Require Import Fcalc_bracket.
Require Import Fcalc_digits.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.

Section Gappa_round.

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

Definition shr (m : positive) (d : positive) :=
 iter_pos d _ shr_aux (rnd_record_mk (Npos m) false false).

Definition round_pos (rdir : rnd_record -> bool)
  (rexp : Z -> Z) (m : positive) (e : Z) :=
 let e' := rexp (e + Zpos (digits m))%Z in
 match (e' - e)%Z with
 | Zpos d =>
   let r := shr m d in
   ((if rdir r then Nsucc (rnd_m r) else rnd_m r), e')
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

Variable rdir : rnd_record -> bool.
Variable good_rdir : good_rdir rdir.

Definition hrndG_aux mx x :=
  match inbetween_loc (Z2R mx) (Z2R mx + 1) x with
  | loc_Exact => (false, false)
  | loc_Inexact Lt => (false, true)
  | loc_Inexact Eq => (true, false)
  | loc_Inexact Gt => (true, true)
  end.

Definition hrndG x :=
  let mx := Zfloor x in
  let m := ZtoN mx in
  let l := inbetween_loc (Z2R mx) (Z2R mx + 1) x in
  let r := let (r, s) := hrndG_aux mx x in rnd_record_mk m r s in
  if rdir r then Zceil x else Zfloor x.

Lemma hrndG_DN :
  forall x,
  rdir (rnd_record_mk (ZtoN (Zfloor x)) true true) = false ->
  hrndG x = Zfloor x.
Proof.
intros x Hx1.
destruct (good_rdir (ZtoN (Zfloor x))) as (Hx2, (Hx3, Hx4)).
rewrite Hx1 in Hx4.
destruct Hx4 as [Hx4|Hx4] ; try easy.
rewrite Hx4 in Hx3.
destruct Hx3 as [Hx3|Hx3] ; try easy.
unfold hrndG.
destruct (hrndG_aux (Zfloor x) x) as ([|],[|]) ;
  now rewrite ?Hx1, ?Hx2, ?Hx3, ?Hx4.
Qed.

Lemma hrndG_UP :
  forall x,
  rdir (rnd_record_mk (ZtoN (Zfloor x)) false true) = true ->
  hrndG x = Zceil x.
Proof.
intros x Hx1.
destruct (good_rdir (ZtoN (Zfloor x))) as (Hx2, (Hx3, Hx4)).
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
  forall x,
  ( forall b, rdir (rnd_record_mk (ZtoN (Zfloor x)) b true) = b ) ->
  hrndG x = Znearest (fun x => rdir (rnd_record_mk (ZtoN x) true false)) x.
Proof.
intros x Hx1.
destruct (good_rdir (ZtoN (Zfloor x))) as (Hx2, _).
unfold hrndG, hrndG_aux.
destruct (inbetween_spec _ _ x (bracket_aux _)) as [Hx4|l Hx4 Hx5].
rewrite Hx2.
rewrite Hx4 at 2.
now rewrite Znearest_Z2R.
unfold Znearest.
rewrite Rcompare_floor_ceil_mid with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
rewrite Rcompare_middle.
rewrite Zceil_floor_neq with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
rewrite Z2R_plus. simpl Z2R.
rewrite Hx5.
now case l ; rewrite ?Hx1, ?Hx2.
Qed.

Lemma hrndG_monotone :
  forall x y, (x <= y)%R -> (hrndG x <= hrndG y)%Z.
Proof.
intros x y Hxy.
destruct (Z_eq_dec (Zfloor x) (Zfloor y)) as [H|H].
(* *)
case_eq (rdir (rnd_record_mk (ZtoN (Zfloor x)) true true)) ; intros Hb1.
case_eq (rdir (rnd_record_mk (ZtoN (Zfloor x)) false true)) ; intros Hb2.
(* . *)
rewrite hrndG_UP with (1 := Hb2).
rewrite H in Hb2.
rewrite hrndG_UP with (1 := Hb2).
now apply Zceil_le.
(* . *)
assert (Hb3: forall b, rdir (rnd_record_mk (ZtoN (Zfloor x)) b true) = b).
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
rewrite Z2R_plus.
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
  forall n, hrndG (Z2R n) = n.
Proof.
intros n.
unfold hrndG.
case rdir.
apply Zceil_Z2R.
apply Zfloor_Z2R.
Qed.

Lemma hrndG_pos :
  forall x, (0 <= x)%R -> (0 <= hrndG x)%Z.
Proof.
intros x Hx.
rewrite <- (hrndG_Z2R 0).
now apply hrndG_monotone.
Qed.

Definition ZhrndG := mkZround hrndG hrndG_monotone hrndG_Z2R.

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
rewrite Z2R_mult.
rewrite Rcompare_Eq.
destruct (Zfloor ms) as [|p|p] ; try easy.
now rewrite Zmult_comm.
now rewrite <- H.
rewrite H at 2.
change 2%R with (Z2R 2).
rewrite <- Z2R_mult.
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
rewrite <- Z2R_mult, <- Z2R_plus.
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
split ; apply lt_Z2R ; rewrite <- H4 ; rewrite Z2R_mult ; apply Rmult_lt_compat_r.
now apply (Z2R_lt 0 2).
apply H1.
now apply (Z2R_lt 0 2).
now rewrite Z2R_plus.
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
rewrite Z2R_plus, Z2R_mult.
refine (conj _ H2).
apply Rmult_le_compat_r.
now apply (Z2R_le 0 2).
apply Zfloor_lb.
(* ... *)
elim Rlt_not_le with (1 := H4).
rewrite H2.
change (Z2R (Zfloor ms) * 2 + 1)%R with (Z2R (Zfloor ms) * Z2R 2 + Z2R 1)%R.
rewrite <- Z2R_mult, <- Z2R_plus.
rewrite Zfloor_Z2R.
apply Rle_refl.
(* ... *)
replace (Zfloor (ms * 2)) with (1 + 2 * Zfloor ms)%Z.
revert H0.
case (Zfloor ms) ; try easy.
intros p H. now elim H.
apply sym_eq.
apply Zfloor_imp.
rewrite Z2R_plus, Z2R_mult.
split.
rewrite Rplus_comm, Rmult_comm.
now apply Rlt_le.
rewrite 2!Z2R_plus, Z2R_mult.
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
rewrite <- bpow_plus.
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
    Fcore_generic_fmt.round radix2 rexp ZhrndG (F2R (Float radix2 (Zpos m) e)).
Proof.
intros rexp m e.
assert (He: canonic_exponent radix2 rexp (F2R (Float radix2 (Zpos m) e)) = rexp (e + Zpos (digits m))%Z).
rewrite digits2_digits.
rewrite digits_ln_beta. 2: easy.
unfold canonic_exponent.
rewrite ln_beta_F2R. 2: easy.
now rewrite Zplus_comm.
unfold round_pos.
case_eq (rexp (e + Zpos (digits m)) - e)%Z.
(* *)
intros H.
apply sym_eq.
apply round_generic.
apply generic_format_canonic_exponent.
simpl.
rewrite He.
rewrite Zminus_eq with (1 := H).
apply Zle_refl.
(* *)
intros p H.
unfold Fcore_generic_fmt.round, scaled_mantissa.
rewrite He.
unfold F2R, float2R. simpl.
rewrite Rmult_assoc, <- bpow_plus.
assert (rexp (e + Zpos (digits m)) = e + Zpos p)%Z.
omega.
rewrite H0.
ring_simplify (e + -(e + Zpos p))%Z.
apply (f_equal (fun m => Z2R m * _)%R).
unfold hrndG.
rewrite (shr_conversion m p).
simpl.
set (rs := hrndG_aux (Zfloor (P2R m * / Z2R (Zpower_pos 2 p))) (P2R m * / Z2R (Zpower_pos 2 p))).
rewrite (surjective_pairing rs).
simpl.
assert (H1: rdir (rnd_record_mk (ZtoN (Zfloor (P2R m * / Z2R (Zpower_pos 2 p)))) (fst rs) (snd rs)) = true ->
  (Z2R (Zfloor (P2R m * / Z2R (Zpower_pos 2 p))) <> P2R m * / Z2R (Zpower_pos 2 p))%R).
unfold rs, hrndG_aux.
destruct (inbetween_spec _ _ (P2R m * / Z2R (Zpower_pos 2 p)) (bracket_aux _)) as [H1|l H1 H2].
simpl.
intros H2 _.
destruct (good_rdir (ZtoN (Zfloor (P2R m * / Z2R (Zpower_pos 2 p))))) as (H3, _).
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
apply sym_eq.
apply round_generic.
apply generic_format_canonic_exponent.
simpl.
rewrite He.
generalize (Zlt_neg_0 p).
omega.
Qed.

End rndG.

Variable rdir : round_dir.

Definition rndG x :=
  match Rcompare x 0 with
  | Gt => hrndG (rpos rdir) x
  | Lt => Zopp (hrndG (rneg rdir) (-x))
  | _ => Z0
  end.

Lemma rndG_monotone :
  forall x y, (x <= y)%R -> (rndG x <= rndG y)%Z.
Proof.
intros x y Hxy.
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
  forall n, rndG (Z2R n) = n.
Proof.
intros n.
unfold rndG.
change R0 with (Z2R 0).
rewrite Rcompare_Z2R.
rewrite <- Z2R_opp.
rewrite 2!hrndG_Z2R.
rewrite Zopp_involutive.
now case n.
Qed.

Definition ZrndG := mkZround rndG rndG_monotone rndG_Z2R.

Lemma rndG_conversion_aux :
  forall rexp f,
  float2R (round rdir rexp f) = Fcore_generic_fmt.round radix2 rexp ZrndG (float2R f).
Proof.
intros rexp (m, e).
unfold float2R. simpl.
destruct m as [|m|m].
now rewrite 2!F2R_0, round_0.
(* *)
unfold round. simpl.
generalize (hrndG_conversion (rpos rdir) (rpos_good _) rexp m e).
unfold Fcore_generic_fmt.round, ZrndG, rndG. simpl.
rewrite Rcompare_Gt.
intros H.
rewrite <- H.
case round_pos.
intros [|n] z ; simpl.
unfold float2R.
now rewrite 2!F2R_0.
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
unfold Fcore_generic_fmt.round, ZrndG, rndG. simpl.
rewrite Rcompare_Lt.
rewrite canonic_exponent_opp.
rewrite scaled_mantissa_opp.
rewrite Ropp_involutive.
rewrite <- opp_F2R.
intros H.
rewrite <- H.
case round_pos.
intros [|n] z ; simpl.
unfold float2R.
rewrite 2!F2R_0.
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

Record rndG_prop := {
  rndG_g : round_dir;
  rndG_f : Zround;
  rndG_eq : forall x, Zrnd (ZrndG rndG_g) x = Zrnd rndG_f x
}.

Theorem rndG_conversion :
  forall rdir rexp f,
  float2R (round (rndG_g rdir) rexp f) = Fcore_generic_fmt.round radix2 rexp (rndG_f rdir) (float2R f).
Proof.
intros (rf, rg, req) rexp f.
simpl.
rewrite rndG_conversion_aux.
now apply round_ext.
Qed.

Lemma roundDN_eq :
  forall x,
  Zrnd (ZrndG roundDN) x = Zrnd rndDN x.
Proof.
intros x.
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

Canonical Structure roundDN_cs := Build_rndG_prop _ _ roundDN_eq.

Lemma roundUP_eq :
  forall x,
  Zrnd (ZrndG roundUP) x = Zrnd rndUP x.
Proof.
intros x.
simpl.
unfold rndG.
case Rcompare_spec ; intros H.
rewrite hrndG_DN ; try easy.
apply roundUP.
rewrite H.
apply sym_eq.
exact (Zceil_Z2R 0).
rewrite hrndG_UP ; try easy.
apply roundUP.
Qed.

Canonical Structure roundUP_cs := Build_rndG_prop _ _ roundUP_eq.

Lemma roundZR_eq :
  forall x,
  Zrnd (ZrndG roundZR) x = Zrnd rndZR x.
Proof.
intros x.
simpl.
unfold rndG, Ztrunc.
destruct (Rlt_bool_spec x 0) as [Hx|[Hx|Hx]].
rewrite Rcompare_Lt with (1 := Hx).
rewrite hrndG_DN ; try easy.
apply roundZR.
rewrite Rcompare_Gt with (1 := Hx).
rewrite hrndG_DN ; try easy.
apply roundZR.
rewrite <- Hx.
rewrite Rcompare_Eq with (1 := refl_equal _).
apply sym_eq.
exact (Zfloor_Z2R 0).
Qed.

Canonical Structure roundZR_cs := Build_rndG_prop _ _ roundZR_eq.

Lemma roundN_eq :
  forall r f,
  ( forall m, (0 <= m)%Z -> forall b c, rneg r (rnd_record_mk (ZtoN m) b c) = andb b (orb c (negb (f (- (m + 1))%Z))) ) ->
  ( forall m, (0 <= m)%Z -> forall b c, rpos r (rnd_record_mk (ZtoN m) b c) = andb b (orb c (f m)) ) ->
  forall x,
  Zrnd (ZrndG r) x = Zrnd (rndN f) x.
Proof.
intros r f Hn Hp x.
simpl.
destruct (Req_dec (Z2R (Zfloor x)) x) as [H1|H1].
rewrite <- H1.
now rewrite rndG_Z2R, Znearest_Z2R.
unfold rndG.
case Rcompare_spec ; intros H2.
(* *)
rewrite hrndG_N. 2: apply rneg_good.
rewrite Znearest_opp, Zopp_involutive.
unfold Znearest.
case Rcompare ; trivial.
rewrite Hn.
simpl.
replace (- (- (Zfloor x + 1) + 1))%Z with (Zfloor x) by ring.
now rewrite negb_involutive.
cut (Zfloor x < 0)%Z. omega.
apply lt_Z2R.
apply Rle_lt_trans with (2 := H2).
apply Zfloor_lb.
intros b.
rewrite Hn.
apply andb_true_r.
apply Zfloor_lub.
apply Rlt_le.
now apply Ropp_0_gt_lt_contravar.
(* *)
rewrite H2.
apply sym_eq.
exact (Znearest_Z2R _ 0).
(* *)
rewrite hrndG_N. 2: apply rpos_good.
unfold Znearest.
case Rcompare ; trivial.
rewrite Hp.
apply refl_equal.
apply Zfloor_lub.
now apply Rlt_le.
intros b.
rewrite Hp.
apply andb_true_r.
apply Zfloor_lub.
now apply Rlt_le.
Qed.

Lemma roundNE_eq :
  forall x,
  Zrnd (ZrndG roundNE) x = Zrnd rndNE x.
Proof.
apply roundN_eq ;
  intros m Hm r s ;
  unfold roundNE, GrndNE ; simpl ;
  apply (f_equal (fun v => r && (s || negb v))).
rewrite Zeven_opp, Zeven_plus.
destruct m as [|[m|m|]|] ; simpl ; trivial.
now elim Hm.
destruct m as [|m|m] ; simpl ; trivial.
now elim Hm.
Qed.

Canonical Structure roundNE_cs := Build_rndG_prop _ _ roundNE_eq.

Lemma roundNA_eq :
  forall x,
  Zrnd (ZrndG roundNA) x = Zrnd rndNA x.
Proof.
apply roundN_eq ;
  intros m Hm r s ; simpl.
rewrite Zle_bool_false.
now rewrite orb_comm, andb_comm.
omega.
rewrite Zle_bool_true with (1 := Hm).
now rewrite orb_comm, andb_comm.
Qed.

Canonical Structure roundNA_cs := Build_rndG_prop _ _ roundNA_eq.

End Gappa_round.
