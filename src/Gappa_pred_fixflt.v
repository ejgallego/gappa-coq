From Flocq Require Import Core Sterbenz.
Require Import Gappa_common.
Require Import Gappa_round_aux.

Theorem fix_subset :
  forall x : R, forall xn zn : Z,
  FIX x xn ->
  Zle_bool zn xn = true ->
  FIX x zn.
Proof.
intros x xn zn Hx Hb.
apply fix_le with (1 := Hx).
now apply Zle_bool_imp_le.
Qed.

Theorem flt_subset :
  forall x : R, forall xn zn : positive,
  FLT x xn ->
  Zle_bool (Zpos xn) (Zpos zn) = true ->
  FLT x zn.
Proof.
intros x xn zn Hx Hb.
apply flt_le with (1 := Hx).
now apply Zle_bool_imp_le.
Qed.

Definition fix_of_singleton_bnd_helper (xi : FF) (n : Z) :=
 Zeq_bool (Fnum (lower xi)) (Fnum (upper xi)) &&
 Zeq_bool (Fexp (lower xi)) (Fexp (upper xi)) &&
 Zle_bool n (Fexp (lower xi)).

Theorem fix_of_singleton_bnd :
 forall x : R, forall xi : FF, forall n : Z,
 ABS x xi ->
 fix_of_singleton_bnd_helper xi n = true ->
 FIX x n.
Proof.
intros x xi n (_, (Hx1, Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zeq_bool_correct_t _ _ H1). clear H1. intro H1.
generalize (Zeq_bool_correct_t _ _ H2). clear H2. intro H2.
generalize (Zle_bool_imp_le _ _ H3). clear H3. intro H3.
assert (float2R (lower xi) = Rabs x).
apply Rle_antisym.
exact Hx1.
replace (lower xi) with (upper xi).
exact Hx2.
apply sym_equal.
induction (lower xi). induction (upper xi).
exact (f_equal2 _ H1 H2).
unfold Rabs in H.
induction (Rcase_abs x).
exists (Fopp2 (lower xi)).
split.
rewrite Fopp2_correct.
rewrite <- (Ropp_involutive x).
apply Ropp_eq_compat.
exact H.
exact H3.
exists (lower xi).
exact (conj H H3).
Qed.

Definition flt_of_singleton_bnd_helper (xi : FF) (n : positive) :=
 Zeq_bool (Fnum (lower xi)) (Fnum (upper xi)) &&
 Zeq_bool (Fexp (lower xi)) (Fexp (upper xi)) &&
 Zlt_bool (Z.abs (Fnum (lower xi))) (two_power_pos n).

Theorem flt_of_singleton_bnd :
 forall x : R, forall xi : FF, forall n : positive,
 ABS x xi ->
 flt_of_singleton_bnd_helper xi n = true ->
 FLT x n.
Proof.
intros x xi n (_, (Hx1, Hx2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zeq_bool_correct_t _ _ H1). clear H1. intro H1.
generalize (Zeq_bool_correct_t _ _ H2). clear H2. intro H2.
generalize (Zlt_cases (Z.abs (Fnum (lower xi))) (two_power_pos n)). rewrite H3. rewrite two_power_pos_correct. clear H3. intro H3.
assert (float2R (lower xi) = Rabs x).
apply Rle_antisym.
exact Hx1.
replace (lower xi) with (upper xi).
exact Hx2.
apply sym_equal.
induction (lower xi). induction (upper xi).
exact (f_equal2 _ H1 H2).
unfold Rabs in H.
induction (Rcase_abs x).
exists (Fopp2 (lower xi)).
split.
rewrite Fopp2_correct.
rewrite <- (Ropp_involutive x).
apply Ropp_eq_compat.
exact H.
simpl.
rewrite Zabs_Zopp.
exact H3.
exists (lower xi).
exact (conj H H3).
Qed.

Theorem neg_fix :
  forall x : R, forall xn zn : Z,
  FIX x xn ->
  Zle_bool zn xn = true ->
  FIX (-x)%R zn.
Proof.
intros x xn zn [fx [Hx1 Hx2]] Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Fopp2 fx).
split.
rewrite <- Hx1.
apply Fopp2_correct.
now apply Z.le_trans with xn.
Qed.

Theorem abs_fix :
  forall x : R, forall xn zn : Z,
  FIX x xn ->
  Zle_bool zn xn = true ->
  FIX (Rabs x) zn.
Proof.
intros x xn zn [[mx ex] [Hx1 Hx2]] Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Float2 (Z.abs mx) ex).
split.
rewrite <- Hx1.
apply F2R_Zabs.
now apply Z.le_trans with xn.
Qed.

Definition add_fix_helper (xn yn zn : Z) :=
 Zle_bool zn xn &&
 Zle_bool zn yn.

Theorem add_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x + y)%R zn.
Proof.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). clear H1. intro H1.
generalize (Zle_bool_imp_le _ _ H2). clear H2. intro H2.
exists (Fplus2 fx fy).
split.
rewrite <- Hx1.
rewrite <- Hy1.
apply Fplus2_correct.
unfold Fplus2, Fshift2.
case (Fexp fx - Fexp fy)%Z ; intros.
exact (Z.le_trans _ _ _ H1 Hx2).
exact (Z.le_trans _ _ _ H2 Hy2).
exact (Z.le_trans _ _ _ H1 Hx2).
Qed.

Theorem sub_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 add_fix_helper xn yn zn = true ->
 FIX (x - y)%R zn.
Proof.
intros x y xn yn zn Hx (fy,(Hy1,Hy2)) Hb.
unfold Rminus.
apply (add_fix _ (-y) _ yn zn Hx).
exists (Fopp2 fy).
split.
rewrite <- Hy1.
apply Fopp2_correct.
exact Hy2.
exact Hb.
Qed.

Theorem mul_fix :
 forall x y : R, forall xn yn zn : Z,
 FIX x xn -> FIX y yn ->
 Zle_bool zn (xn + yn) = true ->
 FIX (x * y)%R zn.
Proof.
intros x y xn yn zn (fx,(Hx1,Hx2)) (fy,(Hy1,Hy2)) Hb.
generalize (Zle_bool_imp_le _ _ Hb). clear Hb. intro H1.
exists (Fmult2 fx fy).
split.
rewrite <- Hx1. rewrite <- Hy1.
apply Fmult2_correct.
apply Z.le_trans with (1 := H1).
exact (Zplus_le_compat _ _ _ _ Hx2 Hy2).
Qed.

Lemma flt_abs_aux :
  forall x : R, forall xn : positive,
  FLT (Rabs x) xn <-> FLT x xn.
Proof.
intros x xn.
unfold Rabs.
case Rcase_abs ; intros Hx.
2: easy.
split ; intros [[mx ex] [Hx1 Hx2]] ;
  exists (Float2 (Z.opp mx) ex) ; split ; simpl.
rewrite <- (Ropp_involutive x), <- Hx1.
apply F2R_Zopp.
now rewrite Zabs_Zopp.
rewrite <- Hx1.
apply F2R_Zopp.
now rewrite Zabs_Zopp.
Qed.

Lemma flt_1_aux :
  forall x y : R, forall yn : positive,
  FLT x 1 -> FLT y yn ->
  FLT (x * y)%R yn.
Proof.
intros x y yn [[mx ex] [<- Hx]] Hy.
destruct mx as [|mx|mx].
rewrite float2_zero, Rmult_0_l.
exists (Float2 Z0 0).
split.
apply float2_zero.
now apply (Zpower_gt_0 radix2 (Zpos yn)).
destruct mx ; try now destruct mx.
destruct Hy as [[my ey] [<- Hy]].
exists (Float2 my (ex + ey)).
split.
2: exact Hy.
unfold float2R ; simpl.
rewrite <- Operations.F2R_mult.
unfold Operations.Fmult.
now rewrite Zmult_1_l.
destruct mx ; try now destruct mx.
destruct Hy as [[my ey] [<- Hy]].
exists (Float2 (-my) (ex + ey)).
split.
2: simpl ; now rewrite Zabs_Zopp.
unfold float2R ; simpl.
rewrite <- Operations.F2R_mult.
unfold Operations.Fmult.
now replace (-1 * my)%Z with (Z.opp my) by ring.
Qed.

Theorem mul_flt :
  forall x y : R, forall xn yn zn : positive,
  FLT x xn -> FLT y yn ->
  Zle_bool (Zpos (if xn =? 1 then yn else if yn =? 1 then xn else xn + yn)%positive) (Zpos zn) = true ->
  FLT (x * y)%R zn.
Proof.
intros x y xn yn zn Hx Hy Hb.
apply Zle_bool_imp_le in Hb.
revert Hb.
apply flt_le.
case Pos.eqb_spec.
intros ->.
now apply flt_1_aux.
intros _.
case Pos.eqb_spec.
intros ->.
rewrite Rmult_comm.
now apply flt_1_aux.
intros _.
destruct Hx as [fx [Hx1 Hx2]].
destruct Hy as [fy [Hy1 Hy2]].
exists (Fmult2 fx fy).
split.
rewrite <- Hx1. rewrite <- Hy1.
apply Fmult2_correct.
change (Z.pow_pos 2 (xn + yn)) with (Zpower radix2 (Zpos xn + Zpos yn)).
rewrite Zpower_plus by easy.
simpl Z.abs.
rewrite Zabs_Zmult.
apply Zmult_lt_compat ; split ;
  try assumption ; apply Zabs_pos.
Qed.

Theorem fix_of_flt_bnd :
 forall x : R, forall xi : FF, forall n : Z, forall p : positive,
 FLT x p -> ABS x xi ->
 Zle_bool (n + Zpos p) (Zpos (digits (pos_of_Z (Fnum (lower xi)))) + Fexp (lower xi))
 && Fpos (lower xi) = true ->
 FIX x n.
Proof.
intros x ((ml,el),xu) n p ((mx,ex),(Hx1,Hx2)) (_,(Hxi,_)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Zle_bool_imp_le _ _ H1). simpl Fnum. simpl Fexp. clear H1. intro H1.
generalize (Fpos_correct _ H2). simpl. clear H2. intro H2.
exists (Float2 mx ex).
split.
exact Hx1.
apply Zplus_le_reg_l with (Zpos p).
rewrite Zplus_comm.
apply Z.le_trans with (1 := H1). clear H1.
rewrite digits2_digits.
assert (H0: (0 < ml)%Z).
apply gt_0_F2R with (1 := H2).
rewrite Zpos_pos_of_Z with (1 := H0).
assert (H0': ml <> Z0).
intros H.
now rewrite H in H0.
rewrite Zdigits_mag with (1 := H0').
rewrite <- mag_F2R with (1 := H0').
apply Z.le_trans with (mag radix2 (Rabs (Float2 mx ex))).
apply mag_le.
now apply F2R_gt_0.
now rewrite Hx1.
rewrite mag_abs.
unfold float2R.
assert (Hx0: mx <> Z0).
intros H.
apply Rle_not_lt with (1 := Hxi).
rewrite <- Hx1, H.
unfold float2R.
rewrite F2R_0, Rabs_R0.
now apply F2R_gt_0.
rewrite mag_F2R with (1 := Hx0).
apply Zplus_le_compat_r.
destruct (mag radix2 (IZR mx)) as (e, He).
simpl.
apply bpow_lt_bpow with radix2.
apply Rle_lt_trans with (Rabs (IZR mx)).
apply He.
now apply (IZR_neq _ 0).
rewrite <- abs_IZR.
rewrite <- IZR_Zpower. 2: easy.
now apply IZR_lt.
Qed.

Theorem flt_of_fix_bnd :
  forall x xi n p,
  FIX x n -> ABS x xi ->
  Zle_bool (Zpos (digits (pos_of_Z (Fnum (upper xi)))) + Fexp (upper xi)) (n + Zpos p) = true ->
  FLT x p.
Proof.
intros x (xl,(mu,eu)) n p ((m,e),(Hx1,Hx2)) Hxi H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
exists (Float2 m e).
split.
exact Hx1.
unfold float2R in Hx1. simpl in Hx1.
simpl Fnum in H. simpl Fexp in H.
apply (lt_F2R radix2 e).
rewrite F2R_Zabs.
apply Rle_lt_trans with (F2R (Float radix2 mu eu)).
simpl. rewrite Hx1.
apply Hxi.
apply Rlt_le_trans with (bpow radix2 (n + Zpos p)).
destruct (Zle_or_lt mu 0) as [Hu|Hu].
apply Rle_lt_trans with R0.
now apply F2R_le_0.
apply bpow_gt_0.
apply Rlt_le_trans with (bpow radix2 (Digits.Zdigits radix2 mu + eu)).
rewrite Zdigits_mag. 2: intros Hu' ; now rewrite Hu' in Hu.
rewrite <- mag_F2R. 2: intros Hu' ; now rewrite Hu' in Hu.
destruct (mag radix2 (F2R (Float radix2 mu eu))) as (e', He).
apply (Rle_lt_trans _ _ _ (RRle_abs _)).
apply He.
apply Rgt_not_eq.
now apply F2R_gt_0.
rewrite <- (Zpos_pos_of_Z _ Hu).
rewrite <- digits2_digits.
now apply bpow_le.
unfold F2R. simpl.
change (Zpower_pos 2 p) with (Zpower radix2 (Zpos p)).
rewrite IZR_Zpower. 2: easy.
rewrite <- bpow_plus.
apply bpow_le.
rewrite Zplus_comm.
now apply Zplus_le_compat_l.
Qed.

Definition sub_flt_helper (xn yn zn : positive) (xyi : FF) :=
  Zle_bool (Zpos xn) (Zpos zn) &&
  Zle_bool (Zpos yn) (Zpos zn) &&
  Fle2 (Float2 (-1) (-1)) (lower xyi) &&
  Fle2 (upper xyi) (Float2 1 0).

Theorem sub_flt :
  forall x y xn yn xyi zn,
  FLT x xn -> FLT y yn -> REL x y xyi ->
  sub_flt_helper xn yn zn xyi = true ->
  FLT (x - y) zn.
Proof.
intros x y xn yn xyi zn Hx Hy (eps,((Hxy1,Hxy2),Hxy3)) Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H3). clear H3. intro H3.
generalize (Fle2_correct _ _ H4). clear H4. intro H4.
destruct (total_order_T y 0) as [[Zy|Zy]|Zy].
(* *)
apply <- FLT_iff_generic.
unfold Rminus.
rewrite <- (Ropp_involutive x), Rplus_comm.
apply sterbenz.
now apply FLX_exp_valid.
apply FLX_exp_monotone.
apply generic_format_opp.
apply -> FLT_iff_generic.
now apply flt_subset with yn.
apply generic_format_opp.
apply -> FLT_iff_generic.
now apply flt_subset with xn.
rewrite Hxy3, <- Ropp_mult_distr_l_reverse.
unfold Rdiv.
rewrite (Rmult_comm 2), 2!Rmult_assoc.
pattern (-y)%R at 2 3 ; rewrite <- Rmult_1_r.
assert (Zy': (0 <= -y)%R).
apply Rlt_le.
now apply Ropp_0_gt_lt_contravar.
split ; apply Rmult_le_compat_l ; try easy.
apply Rmult_le_reg_r with 2%R.
now apply IZR_lt.
rewrite Rmult_assoc, Rinv_l, Rmult_1_l, Rmult_1_r.
apply (Rplus_le_compat_l _ _ 1%R).
apply Rle_trans with (1 := Hxy2).
now rewrite <- (Rmult_1_r 1).
apply Rgt_not_eq.
now apply IZR_lt.
replace 1%R with ((1 + -1 / 2)*2)%R at 1 by field.
apply Rmult_le_compat_r.
now apply IZR_le.
apply Rplus_le_compat_l.
now apply Rle_trans with (2 := Hxy1).
(* *)
rewrite Zy, Rminus_0_r.
now apply flt_subset with xn.
(* *)
apply <- FLT_iff_generic.
apply sterbenz.
now apply FLX_exp_valid.
apply FLX_exp_monotone.
apply -> FLT_iff_generic.
now apply flt_subset with xn.
apply -> FLT_iff_generic.
now apply flt_subset with yn.
rewrite Hxy3.
unfold Rdiv.
rewrite (Rmult_comm 2).
assert (Zy': (0 <= y)%R).
now apply Rlt_le.
split ; apply Rmult_le_compat_l ; try easy.
replace (/2)%R with (1 + -1/2)%R by field.
apply Rplus_le_compat_l.
now apply Rle_trans with (2 := Hxy1).
apply (Rplus_le_compat_l _ _ 1%R).
apply Rle_trans with (1 := Hxy2).
now rewrite <- (Rmult_1_r 1).
Qed.

Theorem sub_flt_rev :
  forall x y xn yn xyi zn,
  FLT x xn -> FLT y yn -> REL x y xyi ->
  sub_flt_helper xn yn zn xyi = true ->
  FLT (y - x) zn.
Proof.
intros x y xn yn xyi zn Hx Hy Hxy Hb.
apply <- FLT_iff_generic.
rewrite <- Ropp_minus_distr.
apply generic_format_opp.
apply -> FLT_iff_generic.
eapply sub_flt ; eassumption.
Qed.
