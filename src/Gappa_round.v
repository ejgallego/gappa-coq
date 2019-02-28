Require Import Decidable.
Require Import Bool.
Require Import ZArith.
Require Import Reals.
From Flocq Require Import Core Bracket Digits.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.

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
 iter_pos shr_aux d (rnd_record_mk (Npos m) false false).

Definition round_pos (rdir : rnd_record -> bool)
  (rexp : Z -> Z) (m : positive) (e : Z) :=
 let e' := rexp (e + Zpos (digits m))%Z in
 match (e' - e)%Z with
 | Zpos d =>
   let r := shr m d in
   ((if rdir r then N.succ (rnd_m r) else rnd_m r), e')
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
  (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
Proof.
split.
apply Zfloor_lb.
apply Zfloor_ub.
Qed.

Variable rdir : rnd_record -> bool.
Variable good_rdir : good_rdir rdir.

Definition hrndG_aux mx x :=
  match inbetween_loc (IZR mx) (IZR mx + 1) x with
  | loc_Exact => (false, false)
  | loc_Inexact Lt => (false, true)
  | loc_Inexact Eq => (true, false)
  | loc_Inexact Gt => (true, true)
  end.

Definition hrndG x :=
  let mx := Zfloor x in
  let m := ZtoN mx in
  let l := inbetween_loc (IZR mx) (IZR mx + 1) x in
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
now rewrite Zceil_IZR.
now case l ; rewrite ?Hx1, ?Hx3, ?Hx4.
Qed.

Lemma hrndG_N :
  forall x,
  ( forall b, rdir (rnd_record_mk (ZtoN (Zfloor x)) b true) = b ) ->
  hrndG x = Znearest (fun x => rdir (rnd_record_mk (ZtoN x) true false)) x.
Proof with auto with typeclass_instances.
intros x Hx1.
destruct (good_rdir (ZtoN (Zfloor x))) as (Hx2, _).
unfold hrndG, hrndG_aux.
destruct (inbetween_spec _ _ x (bracket_aux _)) as [Hx4|l Hx4 Hx5].
rewrite Hx2.
rewrite Hx4 at 2.
rewrite Zrnd_IZR...
unfold Znearest.
rewrite Rcompare_floor_ceil_middle with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
rewrite Rcompare_middle.
rewrite Zceil_floor_neq with (1 := Rlt_not_eq _ _ (proj1 Hx4)).
rewrite plus_IZR.
rewrite Hx5.
now case l ; rewrite ?Hx1, ?Hx2.
Qed.

Instance valid_rnd_hG : Valid_rnd hrndG.
Proof with auto with typeclass_instances.
split.
(* monotone *)
intros x y Hxy.
destruct (Z.eq_dec (Zfloor x) (Zfloor y)) as [H|H].
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
apply Zrnd_le...
(* . *)
rewrite hrndG_DN with (1 := Hb1).
rewrite H in Hb1.
rewrite hrndG_DN with (1 := Hb1).
now apply Zfloor_le.
(* *)
apply Z.le_trans with (Zceil x).
unfold hrndG.
case rdir.
apply Z.le_refl.
apply le_IZR.
exact (Rle_trans _ _ _ (Zfloor_lb x) (Zceil_ub x)).
apply Z.le_trans with (Zfloor y).
apply Z.le_trans with (Zfloor x + 1)%Z.
apply Zceil_glb.
rewrite plus_IZR.
apply Rlt_le.
apply Zfloor_ub.
generalize (Zfloor_le x y Hxy).
omega.
unfold hrndG.
case rdir.
apply le_IZR.
exact (Rle_trans _ _ _ (Zfloor_lb y) (Zceil_ub y)).
apply Z.le_refl.
(* Z2R *)
intros n.
unfold hrndG.
case rdir.
apply Zceil_IZR.
apply Zfloor_IZR.
Qed.

Lemma hrndG_pos :
  forall x, (0 <= x)%R -> (0 <= hrndG x)%Z.
Proof with auto with typeclass_instances.
intros x Hx.
rewrite <- (Zrnd_IZR hrndG 0).
apply Zrnd_le...
Qed.

Lemma shr_conversion :
  forall m d,
  shr m d = let (r, s) := hrndG_aux (Zfloor (IZR (Zpos m) * bpow radix2 (- Zpos d))) (IZR (Zpos m) * bpow radix2 (- Zpos d)) in
    rnd_record_mk (ZtoN (Zfloor (IZR (Zpos m) * bpow radix2 (- Zpos d)))) r s.
Proof.
intros m d.
unfold shr.
rewrite iter_pos_nat.
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P d).
induction (nat_of_P d).
(* *)
simpl.
rewrite Rmult_1_r.
rewrite Zfloor_IZR.
unfold hrndG_aux, inbetween_loc.
now rewrite Rcompare_Eq.
(* *)
rewrite iter_nat_S.
rewrite IHn. clear IHn.
unfold hrndG_aux.
set (ms := (IZR (Zpos m) * bpow radix2 (- Z_of_nat (S n)))%R).
replace (IZR (Zpos m) * bpow radix2 (- Z_of_nat n))%R with (ms * 2)%R.
assert (H0: (0 <= Zfloor ms)%Z).
apply Zfloor_lub.
unfold ms.
apply Rmult_le_pos.
now apply IZR_le.
apply bpow_ge_0.
clearbody ms. clear -H0.
destruct (inbetween_spec _ _ ms (bracket_aux _)) as [H|l H1 H2].
(* . *)
replace (Zfloor (ms * 2)) with (Zfloor ms * 2)%Z.
unfold inbetween_loc.
rewrite mult_IZR.
rewrite Rcompare_Eq.
destruct (Zfloor ms) as [|p|p] ; try easy.
now rewrite Zmult_comm.
now rewrite <- H.
rewrite H at 2.
rewrite <- mult_IZR.
now rewrite Zfloor_IZR.
(* . *)
unfold inbetween_loc.
assert (H3: Rcompare (ms * 2) (IZR (Zfloor ms) * 2 + 1) = l).
rewrite <- (Rcompare_mult_r 2) in H2.
now replace (IZR (Zfloor ms) * 2 + 1)%R with ((IZR (Zfloor ms) + (IZR (Zfloor ms) + 1)) / 2 * 2)%R by field.
now apply IZR_lt.
clear H2. rewrite <- H3. clear H3.
case Rcompare_spec ; intros H4.
elim Rlt_not_le with (1 := H4).
apply Zfloor_lb.
(* .. *)
unfold shr_aux. simpl.
rewrite H4.
rewrite <- mult_IZR, <- plus_IZR.
rewrite Rcompare_IZR.
rewrite <- H4.
replace (Zfloor (ms * 2)) with (1 + 2 * Zfloor ms)%Z.
rewrite Zcompare_Eq.
clear -H0.
destruct (Zfloor ms) as [|p|p] ; [easy|easy|].
now elim H0.
now rewrite Zmult_comm, Zplus_comm.
clear -H1 H4.
assert (Zfloor ms * 2 < Zfloor (ms * 2) < (Zfloor ms + 1) * 2)%Z.
split ; apply lt_IZR ; rewrite <- H4 ; rewrite mult_IZR ; apply Rmult_lt_compat_r.
now apply IZR_lt.
apply H1.
now apply IZR_lt.
now rewrite plus_IZR.
omega.
(* .. *)
set (rs := match Rcompare (ms * 2) ((IZR (Zfloor (ms * 2)) + (IZR (Zfloor (ms * 2)) + 1)) / 2) with
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
rewrite plus_IZR, mult_IZR.
refine (conj _ H2).
apply Rmult_le_compat_r.
now apply IZR_le.
apply Zfloor_lb.
(* ... *)
elim Rlt_not_le with (1 := H4).
rewrite H2.
rewrite <- mult_IZR, <- plus_IZR.
rewrite Zfloor_IZR.
apply Rle_refl.
(* ... *)
replace (Zfloor (ms * 2)) with (1 + 2 * Zfloor ms)%Z.
revert H0.
case (Zfloor ms) ; [easy|easy|].
intros p H. now elim H.
apply sym_eq.
apply Zfloor_imp.
rewrite plus_IZR, mult_IZR.
split.
rewrite Rplus_comm, Rmult_comm.
now apply Rlt_le.
rewrite 2!plus_IZR, mult_IZR.
simpl.
replace (1 + 2 * IZR (Zfloor ms) + 1)%R with ((IZR (Zfloor ms) + 1) * 2)%R by ring.
apply Rmult_lt_compat_r.
now apply IZR_lt.
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
unfold Z.succ.
ring.
Qed.

Lemma Z_of_N_ZtoN :
  forall n, (0 <= n)%Z -> Z_of_N (ZtoN n) = n.
Proof.
intros [|p|p] H ; [easy|easy|].
now elim H.
Qed.

Theorem hrndG_conversion :
  forall rexp m e,
  float2R (tofloat (round_pos rdir rexp m e)) =
    Generic_fmt.round radix2 rexp hrndG (F2R (Float radix2 (Zpos m) e)).
Proof with auto with typeclass_instances.
intros rexp m e.
assert (He: cexp radix2 rexp (F2R (Float radix2 (Zpos m) e)) = rexp (e + Zpos (digits m))%Z).
rewrite digits2_digits.
rewrite Zdigits_mag. 2: easy.
unfold cexp.
rewrite mag_F2R. 2: easy.
now rewrite Zplus_comm.
unfold round_pos.
case_eq (rexp (e + Zpos (digits m)) - e)%Z.
(* *)
intros H.
apply sym_eq.
apply round_generic...
apply generic_format_F2R.
intros _ ; simpl.
rewrite He.
rewrite Zminus_eq with (1 := H).
apply Z.le_refl.
(* *)
intros p H.
unfold Generic_fmt.round, scaled_mantissa.
rewrite He.
unfold F2R, float2R. simpl.
rewrite Rmult_assoc, <- bpow_plus.
assert (rexp (e + Zpos (digits m)) = e + Zpos p)%Z.
omega.
rewrite H0.
ring_simplify (e + -(e + Zpos p))%Z.
apply (f_equal (fun m => IZR m * _)%R).
unfold hrndG.
rewrite (shr_conversion m p).
simpl.
set (rs := hrndG_aux (Zfloor (IZR (Zpos m) * / IZR (Zpower_pos 2 p))) (IZR (Zpos m) * / IZR (Zpower_pos 2 p))).
rewrite (surjective_pairing rs).
simpl.
assert (H1: rdir (rnd_record_mk (ZtoN (Zfloor (IZR (Zpos m) * / IZR (Zpower_pos 2 p)))) (fst rs) (snd rs)) = true ->
  (IZR (Zfloor (IZR (Zpos m) * / IZR (Zpower_pos 2 p))) <> IZR (Zpos m) * / IZR (Zpower_pos 2 p))%R).
unfold rs, hrndG_aux.
destruct (inbetween_spec _ _ (IZR (Zpos m) * / IZR (Zpower_pos 2 p)) (bracket_aux _)) as [H1|l H1 H2].
simpl.
intros H2 _.
destruct (good_rdir (ZtoN (Zfloor (IZR (Zpos m) * / IZR (Zpower_pos 2 p))))) as (H3, _).
now rewrite H2 in H3.
intros _.
now apply Rlt_not_eq.
revert H1.
case rdir.
intros H1.
rewrite Znat.Z_of_N_succ.
rewrite Z_of_N_ZtoN.
apply sym_eq.
apply Zceil_floor_neq.
now apply H1.
apply Zfloor_lub.
now apply (F2R_ge_0 radix2 (Float radix2 (Zpos m) (- (Zpos p)))).
intros _.
rewrite Z_of_N_ZtoN.
apply refl_equal.
apply Zfloor_lub.
now apply (F2R_ge_0 radix2 (Float radix2 (Zpos m) (- (Zpos p)))).
(* *)
intros p H.
apply sym_eq.
apply round_generic...
apply generic_format_F2R.
intros _ ; simpl.
rewrite He.
generalize (Zlt_neg_0 p).
omega.
Qed.

End rndG.

Variable rdir : round_dir.

Definition rndG x :=
  match Rcompare x 0 with
  | Gt => hrndG (rpos rdir) x
  | Lt => Z.opp (hrndG (rneg rdir) (-x))
  | _ => Z0
  end.

Instance valid_rnd_G : Valid_rnd rndG.
Proof.
split.
(* monotone *)
intros x y Hxy.
unfold rndG.
destruct (Rcompare_spec x 0) as [Hx|Hx|Hx].
(* *)
destruct (Rcompare_spec y 0) as [Hy|Hy|Hy].
(* . *)
apply Zopp_le_cancel.
rewrite 2!Z.opp_involutive.
apply Zrnd_le.
apply valid_rnd_hG.
apply rneg_good.
now apply Ropp_le_contravar.
(* . *)
apply Zopp_le_cancel.
rewrite Z.opp_involutive.
apply hrndG_pos.
apply rneg_good.
rewrite <- Ropp_0.
apply Ropp_le_contravar.
now apply Rlt_le.
(* . *)
apply Z.le_trans with Z0.
apply Zopp_le_cancel.
rewrite Z.opp_involutive.
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
apply Z.le_refl.
apply hrndG_pos.
apply rpos_good.
now apply Rlt_le.
(* *)
rewrite Rcompare_Gt.
apply Zrnd_le.
apply valid_rnd_hG.
apply rpos_good.
exact Hxy.
now apply Rlt_le_trans with x.
(* Z2R *)
intros n.
unfold rndG.
rewrite Rcompare_IZR.
rewrite <- opp_IZR.
rewrite 2!Zrnd_IZR.
rewrite Z.opp_involutive.
now case n.
apply valid_rnd_hG.
apply rpos_good.
apply valid_rnd_hG.
apply rneg_good.
Qed.

Lemma rndG_conversion_aux :
  forall rexp f,
  float2R (round rdir rexp f) = Generic_fmt.round radix2 rexp rndG (float2R f).
Proof with auto with typeclass_instances.
intros rexp (m, e).
unfold float2R. simpl.
destruct m as [|m|m].
rewrite 2!F2R_0, round_0...
(* *)
unfold round. simpl.
generalize (hrndG_conversion (rpos rdir) (rpos_good _) rexp m e).
unfold Generic_fmt.round, rndG. simpl.
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
now apply F2R_gt_0.
apply bpow_gt_0.
(* *)
unfold round. simpl.
change (Zneg m) with (- Zpos m)%Z.
rewrite F2R_Zopp.
generalize (hrndG_conversion (rneg rdir) (rneg_good _) rexp m e).
unfold Generic_fmt.round, rndG. simpl.
rewrite Rcompare_Lt.
rewrite cexp_opp.
rewrite scaled_mantissa_opp.
rewrite Ropp_involutive.
rewrite F2R_Zopp.
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
now apply F2R_gt_0.
apply bpow_gt_0.
Qed.

End ZrndG.

Existing Instance valid_rnd_G.

Record rndG_prop := {
  rndG_g : round_dir;
  rndG_f : R -> Z;
  rndG_eq : forall x, rndG rndG_g x = rndG_f x
}.

Theorem rndG_conversion :
  forall rdir rexp f,
  float2R (round (rndG_g rdir) rexp f) = Generic_fmt.round radix2 rexp (rndG_f rdir) (float2R f).
Proof.
intros (rf, rg, req) rexp f.
simpl.
rewrite rndG_conversion_aux.
now apply round_ext.
Qed.

Instance valid_rnd_Gf : forall rdir, Valid_rnd (rndG_f rdir).
Proof with auto with typeclass_instances.
split.
intros x y H.
rewrite <- 2!rndG_eq.
apply Zrnd_le...
intros n.
rewrite <- rndG_eq.
apply Zrnd_IZR...
Qed.

Lemma roundDN_eq :
  forall x,
  rndG roundDN x = Zfloor x.
Proof.
intros x.
simpl.
unfold rndG.
case Rcompare_spec ; intros H.
rewrite hrndG_UP.
unfold Zceil.
rewrite Ropp_involutive.
apply Z.opp_involutive.
apply roundDN.
apply refl_equal.
rewrite H.
apply sym_eq.
apply Zfloor_IZR.
rewrite hrndG_DN ; try easy.
apply roundDN.
Qed.

Canonical Structure roundDN_cs := Build_rndG_prop _ _ roundDN_eq.

Lemma roundUP_eq :
  forall x,
  rndG roundUP x = Zceil x.
Proof.
intros x.
simpl.
unfold rndG.
case Rcompare_spec ; intros H.
rewrite hrndG_DN ; try easy.
apply roundUP.
rewrite H.
apply sym_eq.
apply Zceil_IZR.
rewrite hrndG_UP ; try easy.
apply roundUP.
Qed.

Canonical Structure roundUP_cs := Build_rndG_prop _ _ roundUP_eq.

Lemma roundZR_eq :
  forall x,
  rndG roundZR x = Ztrunc x.
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
apply Zfloor_IZR.
Qed.

Canonical Structure roundZR_cs := Build_rndG_prop _ _ roundZR_eq.

Lemma roundN_eq :
  forall r f,
  ( forall m, (0 <= m)%Z -> forall b c, rneg r (rnd_record_mk (ZtoN m) b c) = andb b (orb c (negb (f (- (m + 1))%Z))) ) ->
  ( forall m, (0 <= m)%Z -> forall b c, rpos r (rnd_record_mk (ZtoN m) b c) = andb b (orb c (f m)) ) ->
  forall x,
  rndG r x = Znearest f x.
Proof with auto with typeclass_instances.
intros r f Hn Hp x.
simpl.
destruct (Req_dec (IZR (Zfloor x)) x) as [H1|H1].
rewrite <- H1.
rewrite 2!Zrnd_IZR...
unfold rndG.
case Rcompare_spec ; intros H2.
(* *)
rewrite hrndG_N. 2: apply rneg_good.
rewrite Znearest_opp, Z.opp_involutive.
unfold Znearest.
case Rcompare ; trivial.
rewrite Hn.
simpl.
replace (- (- (Zfloor x + 1) + 1))%Z with (Zfloor x) by ring.
now rewrite negb_involutive.
cut (Zfloor x < 0)%Z. omega.
apply lt_IZR.
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
apply Zrnd_IZR...
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
  rndG roundNE x = rndNE x.
Proof.
apply roundN_eq ;
  intros m Hm r s ;
  unfold roundNE, GrndNE ; simpl ;
  apply (f_equal (fun v => r && (s || negb v))).
rewrite Z.even_opp, Z.even_add.
now destruct m as [|[m|m|]|].
now destruct m as [|[m|m|]|].
Qed.

Canonical Structure roundNE_cs := Build_rndG_prop _ _ roundNE_eq.

Lemma roundNA_eq :
  forall x,
  rndG roundNA x = rndNA x.
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
