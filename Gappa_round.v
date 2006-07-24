Require Import Classical.
Require Import Decidable.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.
Require Import Gappa_round_def.

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

Lemma float2_shift_p1 :
 forall e : Z, forall m : Z,
 Float2 m (e + 1) = Float2 (m * 2) e :>R.
intros e m.
unfold float2R. simpl.
rewrite powerRZ_add. 2: discrR.
rewrite mult_IZR.
simpl.
replace (IZR 2) with 2%R. 2: apply refl_equal.
ring.
Qed.

Lemma float2_shift_m1 :
 forall e : Z, forall m : Z,
 Float2 m e = Float2 (m * 2) (e - 1) :>R.
intros e m.
pattern e at 1 ; replace e with (e - 1 + 1)%Z. 2: ring.
apply float2_shift_p1.
Qed.

Lemma float2_binade_lt :
 forall m1 m2 : Z, forall e : Z,
 (m1 < m2)%Z -> (Float2 m1 e < Float2 m2 e)%R.
intros m1 m2 e H.
unfold float2R. simpl.
apply Rmult_lt_compat_r.
auto with real.
apply IZR_lt with (1 := H).
Qed.

Lemma float2_binade_le :
 forall m1 m2 : Z, forall e : Z,
 (m1 <= m2)%Z -> (Float2 m1 e <= Float2 m2 e)%R.
intros m1 m2 e H.
unfold float2R. simpl.
apply Rmult_le_compat_r.
auto with real.
apply IZR_le with (1 := H).
Qed.

Lemma float2_binade_eq_reg_aux :
 forall m1 m2 : positive, forall e : Z,
 Float2 (Zpos m1) e = Float2 (Zpos m2) e :>R ->
 m1 = m2.
intros m1 m2 e.
unfold float2R.
simpl.
repeat rewrite <- (Rmult_comm (powerRZ 2 e)).
intros H.
assert (powerRZ 2 e <> 0)%R.
apply powerRZ_NOR.
discrR.
generalize (Rmult_eq_reg_l _ _ _ H H0). clear H. intro H.
generalize (INR_eq _ _ H). clear H. intro H.
rewrite <- (pred_o_P_of_succ_nat_o_nat_of_P_eq_id m1).
rewrite H.
rewrite pred_o_P_of_succ_nat_o_nat_of_P_eq_id.
apply refl_equal.
Qed.

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
replace (Zpos m * 2)%Z with (Zpos (m * 2)).
apply refl_equal.
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
replace (m2 * 2 + 2)%Z with ((m2 + 1) * 2)%Z. 2: ring.
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

Fixpoint digits (m : positive) : positive :=
 match m with
 | xH => xH
 | xI p => Psucc (digits p)
 | xO p => Psucc (digits p)
 end.

Definition digitsN (n : N) :=
 match n with
 | N0 => Z0
 | Npos m => Zpos (digits m)
 end.

Lemma digits_correct :
 forall m : positive,
 (powerRZ 2 (Zpos (digits m) - 1)%Z <= IZR (Zpos m) < powerRZ 2 (Zpos (digits m)))%R.
Admitted.

Lemma digits_float_correct :
 forall m : positive, forall e: Z,
 (Float2 1 (e + Zpos (digits m) - 1)%Z <= Float2 (Zpos m) e < Float2 1 (e + Zpos (digits m))%Z)%R.
intros m e.
generalize (digits_correct m). intros (H1,H2).
unfold float2R. simpl.
repeat rewrite Rmult_1_l.
split.
unfold Zminus.
rewrite <- Zplus_assoc.
rewrite powerRZ_add. 2: discrR.
rewrite Rmult_comm.
apply Rmult_le_compat_r.
auto with real.
exact H1.
rewrite powerRZ_add. 2: discrR.
rewrite Rmult_comm.
apply Rmult_lt_compat_l.
auto with real.
exact H2.
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

Lemma round_constant_xO :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 good_rdir rdir ->
 match round_pos rdir rexp m e with (m1',e1') => Float2 (Z_of_N m1') e1' end =
 match round_pos rdir rexp (xO m) (e - 1) with (m2',e2') => Float2 (Z_of_N m2') e2' end :>R.
intros rdir rexp m e Hdir.
unfold round_pos.
simpl.
rewrite Zpos_succ_morphism.
cutrewrite (e - 1 + Zsucc (Zpos (digits m)) = e + Zpos (digits m))%Z.
2: unfold Zsucc ; ring.
cutrewrite (rexp (e + Zpos (digits m)) - (e - 1) = rexp (e + Zpos (digits m)) - e + 1)%Z.
2: ring.
case (Zle_or_lt (rexp (e + Zpos (digits m)) - e + 1)%Z Z0) ; intro H.
assert (rexp (e + Zpos (digits m)) - e < 0)%Z.
omega.
caseEq (rexp (e + Zpos (digits m)) - e)%Z ; intros.
rewrite H1 in H0.
discriminate H0.
rewrite H1 in H0.
discriminate H0.
assert (Float2 (Z_of_N (Npos m)) e = Float2 (Z_of_N (Npos (xO m))) (e - 1) :>R).
unfold Z_of_N.
rewrite float2_shift_m1.
rewrite Zmult_comm.
apply refl_equal.
caseEq (Zneg p + 1)%Z ; intros.
exact H2.
rewrite Zplus_comm in H3.
destruct p ; discriminate H3.
exact H2.
caseEq (rexp (e + Zpos (digits m)) - e + 1)%Z ; intros.
rewrite H0 in H.
discriminate H.
caseEq (rexp (e + Zpos (digits m)) - e)%Z ; intros.
assert (p = 1%positive).
rewrite H1 in H0.
simpl in H0.
injection H0.
intros. auto.
rewrite H2.
unfold shr, shr_aux.
simpl.
rewrite (proj1 (Hdir (Npos m) (rexp (e + Zpos (digits m))%Z))).
simpl.
cutrewrite (rexp (e + Zpos (digits m)) = e)%Z.
apply refl_equal.
auto with zarith.
unfold shr at 4 5 6.
rewrite iter_nat_of_P.
cutrewrite (nat_of_P p = nat_of_P p0 + 1).
rewrite iter_nat_plus.
simpl.
rewrite <- iter_nat_of_P.
unfold shr_aux at 2 4 6.
simpl.
fold (shr m p0).
apply refl_equal.
rewrite H1 in H0.
fold (Zsucc (Zpos p0)) in H0.
rewrite plus_comm.
unfold plus.
rewrite <- nat_of_P_succ_morphism.
rewrite <- Zpos_succ_morphism in H0.
injection H0.
intros H2.
rewrite H2.
apply refl_equal.
rewrite H1 in H0.
destruct p0 ; discriminate H0.
rewrite H0 in H.
discriminate H.
Qed.

Axiom float2_equal_xO :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (e1 < e2)%Z ->
 Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R ->
 exists p : positive, m1 = xO p.

Lemma round_unicity_aux :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m1 m2 : positive, forall e1 e2 : Z,
 good_rdir rdir -> (e1 < e2)%Z ->
 Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R ->
 match round_pos rdir rexp m1 e1 with (m1',e1') => Float2 (Z_of_N m1') e1' end =
 match round_pos rdir rexp m2 e2 with (m2',e2') => Float2 (Z_of_N m2') e2' end :>R.
intros rdir rexp m1 m2 e1 e2 Hdir He Heq.
assert (exists n : nat, e1 = e2 - Z_of_nat n)%Z.
assert (exists n : nat, e2 - e1 = Z_of_nat n)%Z.
apply IZN.
omega.
generalize H. clear H. intros (n, H).
exists n.
rewrite <- H.
ring.
generalize H. clear H. intros (n, H).
generalize Heq. rewrite H. clear He Heq H e1.
generalize m1. clear m1.
induction n.
intros m1.
simpl.
rewrite Zminus_0_r.
intros H.
generalize (float2_binade_eq_reg_aux _ _ _ H). intros H0.
rewrite H0. clear H H0.
apply refl_equal.
intros m1 Heq.
assert (He: (e2 - Z_of_nat (S n) < e2)%Z).
apply Zlt_minus_simpl_swap.
simpl.
unfold Zlt.
apply refl_equal.
generalize (float2_equal_xO m1 m2 _ e2 He Heq).
intros (p, H). rewrite H in Heq. rewrite H. clear H m1.
assert (e2 - Z_of_nat (S n) = e2 - Z_of_nat n - 1)%Z.
rewrite inj_S.
unfold Zsucc.
ring.
rewrite H in Heq.
rewrite H.
clear H.
rewrite <- round_constant_xO.
2: exact Hdir.
apply (IHn p).
rewrite <- Heq.
replace (Zpos (xO p)) with (Zpos p * 2)%Z.
apply float2_shift_m1.
rewrite Zmult_comm.
apply refl_equal.
Qed.

Lemma round_unicity :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m1 m2 : positive, forall e1 e2 : Z,
 good_rdir rdir ->
 Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R ->
 match round_pos rdir rexp m1 e1 with (m1',e1') => Float2 (Z_of_N m1') e1' end =
 match round_pos rdir rexp m2 e2 with (m2',e2') => Float2 (Z_of_N m2') e2' end :>R.
intros rdir rexp m1 m2 e1 e2 Hdir Heq.
case (Ztrichotomy e1 e2) ; [ intros H | intros [H|H] ].
apply round_unicity_aux with (1 := Hdir) (2 := H) (3 := Heq).
rewrite H in Heq.
generalize (float2_binade_eq_reg_aux _ _ _ Heq).
intros H0.
rewrite H0.
rewrite H.
apply refl_equal.
apply sym_eq.
apply round_unicity_aux with (1 := Hdir).
auto with zarith.
rewrite Heq.
apply refl_equal.
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
replace (Zpos m1 + 1)%Z with (Zpos (Psucc m1)).
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
simpl in *.
rewrite nat_of_P_xO.
rewrite mult_INR.
rewrite Rmult_assoc.
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

Definition pos_of_Z (n : Z) :=
 match n with
 | Zpos p => p
 | _ => xH
 end.

Lemma Zpos_pos_of_Z :
 forall a b : Z, (a < b)%Z ->
 (b - a = Zpos (pos_of_Z (b - a)))%Z.
intros a b H.
assert (0 < b - a)%Z.
omega.
destruct (b - a)%Z ; compute in H0 ; try discriminate H0.
apply refl_equal.
Qed.

Axiom float2_repartition :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 < Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 (e2 < e1)%Z /\ (e1 + Zpos (digits m1) = e2 + Zpos (digits m2))%Z.

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
rewrite <- (Zpos_pos_of_Z _ _ H1).
ring (e2 + (e1 - e2))%Z.
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
rewrite <- (Zpos_pos_of_Z _ _ He).
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
 forall rdir : rnd_record -> Z -> bool,
 forall rexp : Z -> Z,
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
split ; [idtac | split ] ; intros Hf2.
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
rewrite (Zpos_pos_of_Z _ _ H1).
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
rewrite (Zpos_pos_of_Z _ _ H1).
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
rewrite (Zpos_pos_of_Z _ _ H1).
pattern (shr m2 (pos_of_Z (e1 - e2))) at 1 ; rewrite rnd_record_eq.
rewrite (shr_constant_m m1 m2 e1 e2 Hb).
generalize (shr_constant_rs m1 m2 e1 e2 Hb).
intros (_,(_,Hrs)).
rewrite (proj1 (Hrs (proj1 Hf2))).
rewrite (proj2 (Hrs (proj1 Hf2))).
apply refl_equal.
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
rewrite <- Zpos_pos_of_Z. ring.
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

Lemma round_monotone_local :
 forall rdir : rnd_record -> Z -> bool,
 forall rexp : Z -> Z,
 good_rdir rdir ->
 good_rexp rexp ->
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) = e1)%Z ->
 forall m2 m3 : positive, forall e2 e3 : Z,
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2 <= Float2 (Zpos m1 + 1) e1)%R ->
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m3) e3 <= Float2 (Zpos m1 + 1) e1)%R ->
 (Float2 (Zpos m2) e2 <= Float2 (Zpos m3) e3)%R ->
 (match round_pos rdir rexp m2 e2 with (m2',e2') => Float2 (Z_of_N m2') e2' end <=
  match round_pos rdir rexp m3 e3 with (m3',e3') => Float2 (Z_of_N m3') e3' end)%R.
unfold good_rdir.
intros rdir rexp Hgd Hge m1 e1 He1 m2 m3 e2 e3 (Hb2a,[Hb2b|Hb2b]) (Hb3a,[Hb3b|Hb3b]) Hf.
generalize (round_constant rdir rexp m1 e1 He1 m3 e3).
generalize (round_constant rdir rexp m1 e1 He1 m2 e2).
intros Hc2 Hc3.
generalize (bracket_case m1 m2 e1 e2 (conj Hb2a Hb2b)).
generalize (bracket_case m1 m3 e1 e3 (conj Hb3a Hb3b)).
intros [H3|[H3|[H3|H3]]].
(* *)
intros [H2|H2].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_unicity rdir rexp m3 m1 e3 e1 Hgd H3).
auto with real.
elim Rle_not_lt with (1 := Hf).
rewrite H3.
generalize H2. clear H2. intros [H2|[H2|H2]].
exact (proj1 H2).
rewrite H2.
rewrite (float2_shift_m1 e1).
apply float2_binade_lt.
auto with zarith.
apply Rlt_trans with (2 := proj1 H2).
rewrite (float2_shift_m1 e1).
apply float2_binade_lt.
auto with zarith.
(* *)
intros [H2|[H2|H2]].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_rexp_exact rdir rexp m1 e1).
2: apply Zeq_le with (1 := He1).
rewrite (proj1 Hc3 H3).
apply float2_binade_le.
case (rdir (rnd_record_mk (Npos m1) false true)) ; simpl ;
try rewrite Zpos_succ_morphism ; auto with zarith.
rewrite (proj1 Hc2 H2).
rewrite (proj1 Hc3 H3).
apply float2_binade_le.
auto with zarith.
elim Rle_not_lt with (1 := Hf).
apply Rlt_le_trans with (1 := proj2 H3).
generalize H2. clear H2. intros [H2|H2].
rewrite H2.
auto with real.
apply Rlt_le with (1 := proj1 H2).
(* *)
intros [H2|[H2|[H2|H2]]].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_rexp_exact rdir rexp m1 e1).
rewrite (proj1 (proj2 Hc3) H3).
apply float2_binade_le.
case (rdir (rnd_record_mk (Npos m1) true false) e1) ; simpl ;
try rewrite Zpos_succ_morphism ; auto with zarith.
apply Zeq_le with (1 := He1).
rewrite (proj1 Hc2 H2).
rewrite (proj1 (proj2 Hc3) H3).
apply float2_binade_le.
caseEq (rdir (rnd_record_mk (Npos m1) false true) e1) ;
caseEq (rdir (rnd_record_mk (Npos m1) true false) e1) ;
intros H4 H5 ; simpl ; try rewrite Zpos_succ_morphism ;
auto with zarith ; generalize (Hgd (Npos m1) e1).
intros (_,([H6|H6],_)).
rewrite H6 in H5.
discriminate H5.
rewrite H6 in H4.
discriminate H4.
rewrite (proj1 (proj2 Hc2) H2).
rewrite (proj1 (proj2 Hc3) H3).
auto with real.
elim Rle_not_lt with (1 := Hf).
rewrite H3.
exact (proj1 H2).
rewrite (proj2 (proj2 Hc3) H3).
intros [H2|[H2|[H2|H2]]].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_rexp_exact rdir rexp m1 e1).
apply float2_binade_le.
case (rdir (rnd_record_mk (Npos m1) true true)) ;
simpl ; try rewrite Zpos_succ_morphism ; auto with zarith.
apply Zeq_le with (1 := He1).
rewrite (proj1 Hc2 H2).
apply float2_binade_le.
caseEq (rdir (rnd_record_mk (Npos m1) false true) e1) ;
caseEq (rdir (rnd_record_mk (Npos m1) true true) e1) ;
intros H4 H5 ; simpl ; try rewrite Zpos_succ_morphism ;
auto with zarith ; generalize (Hgd (Npos m1) e1).
intros (_,([H6|H6],[H7|H7])).
rewrite H6 in H5.
discriminate H5.
rewrite H6 in H5.
discriminate H5.
rewrite H6 in H7.
discriminate H7.
rewrite H4 in H7.
discriminate H7.
rewrite (proj1 (proj2 Hc2) H2).
apply float2_binade_le.
caseEq (rdir (rnd_record_mk (Npos m1) true false) e1) ;
caseEq (rdir (rnd_record_mk (Npos m1) true true) e1) ;
intros H4 H5 ; simpl ; try rewrite Zpos_succ_morphism ;
auto with zarith ; generalize (Hgd (Npos m1) e1).
intros (_,(_,[H6|H6])).
rewrite H6 in H5.
discriminate H5.
rewrite H6 in H4.
discriminate H4.
rewrite (proj2 (proj2 Hc2) H2).
auto with real.
(* *)
generalize (rexp_succ rexp Hge m1 e1 (Zeq_le _ _ He1)).
rewrite <- Hb3b.
intros (m4,(e4,(Hb4,He4))).
rewrite <- (round_unicity rdir rexp m4 m3 e4 e3 Hgd Hb4).
rewrite (round_rexp_exact rdir rexp m4 e4 He4).
simpl.
rewrite Hb4.
rewrite Hb3b.
generalize (round_constant rdir rexp m1 e1 He1 m2 e2).
intros Hc2.
generalize (bracket_case m1 m2 e1 e2 (conj Hb2a Hb2b)).
assert (H4: (Float2 (Zpos m1) e1 <= Float2 (Zpos m1 + 1) e1)%R).
apply float2_binade_le.
auto with zarith.
assert (H5: (Float2 (Zpos (Psucc m1)) e1 <= Float2 (Zpos m1 + 1) e1)%R).
apply float2_binade_le.
rewrite Zpos_succ_morphism.
apply Zle_refl.
intros [H2|[H2|[H2|H2]]].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_rexp_exact rdir rexp m1 e1).
exact H4.
apply Zeq_le with (1 := He1).
rewrite (proj1 Hc2 H2).
case (rdir (rnd_record_mk (Npos m1) false true)).
exact H5.
exact H4.
rewrite (proj1 (proj2 Hc2) H2).
case (rdir (rnd_record_mk (Npos m1) true false)).
exact H5.
exact H4.
rewrite (proj2 (proj2 Hc2) H2).
case (rdir (rnd_record_mk (Npos m1) true true)).
exact H5.
exact H4.
(* *)
elim Rle_not_lt with (1 := Hf).
rewrite Hb2b.
exact Hb3b.
(* *)
apply Req_le.
apply round_unicity with (1 := Hgd).
rewrite Hb3b.
exact Hb2b.
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

Axiom plouf : forall P : Prop, P.

Lemma round_monotone_underflow :
 forall rdir : rnd_record -> Z -> bool,
 forall rexp : Z -> Z,
 good_rdir rdir ->
 good_rexp rexp ->
 forall k : Z,
 rexp k = k ->
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 < Float2 1 k)%R ->
 (Float2 (Zpos m2) e2 < Float2 1 k)%R ->
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2)%R ->
 (match round_pos rdir rexp m1 e1 with (m1',e1') => Float2 (Z_of_N m1') e1' end <=
  match round_pos rdir rexp m2 e2 with (m2',e2') => Float2 (Z_of_N m2') e2' end)%R.
intros rdir rexp Hgd Hge k Hk m1 m2 e1 e2 Hf1 Hf2 Hf.
cut (exists m3, exists m4, exists e,
     Float2 (Zpos m3) e = Float2 (Zpos m1) e1 :>R /\
     Float2 (Zpos m4) e = Float2 (Zpos m2) e2 :>R).
intros (m3,(m4,(e,(Hr1,Hr2)))).
rewrite <- Hr1 in Hf1. rewrite <- Hr2 in Hf2.
rewrite <- (round_unicity rdir rexp m3 m1 e e1 Hgd Hr1).
rewrite <- (round_unicity rdir rexp m4 m2 e e2 Hgd Hr2).
cut (forall m : positive,
     (Float2 (Zpos m) e < Float2 1 k)%R ->
     (e + Zpos (digits m) <= k)%Z).
intro Hke.
generalize (Hke m3 Hf1). intro Hk1.
generalize (Hke m4 Hf2). intro Hk2.
unfold round_pos.
rewrite (rexp_underflow rexp Hge k Hk _ Hk1).
rewrite (rexp_underflow rexp Hge k Hk _ Hk2).
assert (e < k)%Z.
generalize (Zgt_pos_0 (digits m3)).
omega.
rewrite (Zpos_pos_of_Z _ _ H).
clear H Hke Hk1 Hk2.
apply float2_binade_le.
rewrite <- Hr1 in Hf. rewrite <- Hr2 in Hf.
assert (Zpos m3 <= Zpos m4)%Z.
unfold float2R in Hf.
simpl in Hf.
repeat rewrite <- (Rmult_comm (powerRZ 2 e)) in Hf.
assert (0 < powerRZ 2 e)%R.
apply powerRZ_lt.
auto with real.
generalize (Rmult_le_reg_l _ _ _ H Hf).
clear H. intro H.
generalize (INR_le _ _ H).
clear H. intros H H0.
generalize (nat_of_P_gt_Gt_compare_morphism _ _ H0).
intuition.
generalize H.
generalize m3.
generalize m4.
generalize (pos_of_Z (k - e)).
clear Hr1 Hr2 Hf1 Hf2 Hf Hge Hk rexp H m3 m4 m1 m2 e e1 e2.
intros d m2 m1 H.
assert (forall s : rnd_record,
  Z_of_N (if rdir s k then Nsucc (rnd_m s) else rnd_m s) =
  if rdir s k then Z_of_N (Nsucc (rnd_m s)) else Z_of_N (rnd_m s)).
intro s. case (rdir s k) ; apply refl_equal.
repeat rewrite H0. clear H0.
cut (Z_of_N (rnd_m (shr m1 d)) <= Z_of_N (rnd_m (shr m2 d)))%Z.
intro H0.
assert (forall x, Z_of_N (Nsucc x) = (Z_of_N x + 1)%Z).
intro x.
case x.
apply refl_equal.
unfold Nsucc, Z_of_N.
intros p.
exact (Zpos_succ_morphism p).
repeat rewrite H1.
case (Zle_lt_or_eq _ _ H0) ; clear H0 ; intro H0.
case (rdir (shr m1 d) k) ; case (rdir (shr m2 d) k) ; auto with zarith.
caseEq (rdir (shr m1 d) k) ; caseEq (rdir (shr m2 d) k) ; auto with zarith.
generalize (Hgd (rnd_m (shr m1 d)) k).
apply plouf.
apply plouf.
apply plouf.
generalize (Fshift2_correct (Float2 (Zpos m1) e1) (Float2 (Zpos m2) e2)).
caseEq (Fshift2 (Float2 (Zpos m1) e1) (Float2 (Zpos m2) e2)).
intros (mx, my) e H (Hx, Hy).
exists (pos_of_Z mx).
exists (pos_of_Z my).
exists e.
cut (Zpos (pos_of_Z mx) = mx /\ Zpos (pos_of_Z my) = my).
intro H0. rewrite (proj1 H0). rewrite (proj2 H0).
exact (conj Hx Hy).
replace mx with (fst (fst (Fshift2 (Float2 (Zpos m1) e1) (Float2 (Zpos m2) e2)))).
2: rewrite H ; apply refl_equal.
replace my with (snd (fst (Fshift2 (Float2 (Zpos m1) e1) (Float2 (Zpos m2) e2)))).
2: rewrite H ; apply refl_equal.
unfold Fshift2.
simpl.
case (e1 - e2)%Z ; intros ; split ; apply refl_equal.
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
replace (Zpos (xO p)) with (2 * Zpos p)%Z. 2: apply refl_equal.
replace (Zpos (xI p)) with (2 * Zpos p + 1)%Z. 2: apply refl_equal.
auto with zarith.
apply Zle_refl.
rewrite H4 in H0.
unfold digits, nat_of_P in H0.
simpl in H0.
elim (lt_irrefl _ H0).
apply Rlt_le_trans with (1 := proj2 H2).
apply float2_binade_le.
caseEq m2 ; intros.
replace (Zpos (xO (p + 1))) with (2 * (Zpos p + 1))%Z. 2: apply refl_equal.
replace (Zpos (xI p) + 1)%Z with (2 * Zpos p + 1 + 1)%Z. 2: apply refl_equal.
auto with zarith.
replace (Zpos (xO p) + 1)%Z with (2 * Zpos p + 1)%Z. 2: apply refl_equal.
replace (Zpos (xO (p + 1))) with (2 * (Zpos p + 1))%Z. 2: apply refl_equal.
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

Lemma rexp_case :
 forall rexp : Z -> Z, good_rexp rexp ->
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) <= e1)%Z \/
 let e2 := rexp (e1 + Zpos (digits m1))%Z in
 ((e1 < e2)%Z /\ rexp e2 = e2 /\
  rnd_m (shr m1 (pos_of_Z (e2 - e1))) = N0 /\
  (Float2 (Zpos m1) e1 < Float2 1 e2)%R) \/
 exists m2 : positive,
 Npos m2 = rnd_m (shr m1 (pos_of_Z (e2 - e1))) /\
 rexp (e2 + Zpos (digits m2))%Z = e2 /\
 (Float2 (Zpos m2) e2 <= Float2 (Zpos m1) e1 < Float2 (Zpos m2 + 1) e2)%R.
intros rexp Hg m1 e1.
set (e2 := rexp (e1 + Zpos (digits m1))%Z).
case (Z_lt_le_dec e1 e2) ; intro He1 ; [ right | left ].
2: exact He1.
intros e3. unfold e3. clear e3.
case (Z_lt_le_dec e2 (e1 + Zpos (digits m1))%Z) ; intro He1' ; [ right | left ].
cut (e2 - e1 < Zpos (digits m1))%Z. 2: omega.
rewrite (Zpos_pos_of_Z _ _ He1).
intro H.
generalize (nat_of_P_lt_Lt_compare_morphism _ _ H).
clear H. intro H.
generalize (rexp_case_aux m1 e1 (nat_of_P (pos_of_Z (e2 - e1))) H).
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite <- Zpos_pos_of_Z. 2: exact He1.
cutrewrite (e1 + (e2 - e1) = e2)%Z. 2: ring.
cutrewrite (P_of_succ_nat (pred (nat_of_P (pos_of_Z (e2 - e1)))) = pos_of_Z (e2 - e1)).
clear H. intros (m2,H).
exists m2.
split.
rewrite (proj1 H).
caseEq (nat_of_P (pos_of_Z (e2 - e1))).
generalize (ZL4 (pos_of_Z (e2 - e1))).
intros (h, H0) H1. rewrite H0 in H1. discriminate H1.
unfold shr.
intros n H0.
repeat rewrite iter_nat_of_P.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite H0.
apply refl_equal.
split. 2: exact (proj1 (proj2 H)).
cutrewrite (Zpos (digits m2) = Zpos (digits m1) - (e2 - e1))%Z.
unfold e2.
apply (f_equal rexp).
ring.
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P (digits m1)).
rewrite <- (proj2 (proj2 H)).
rewrite inj_plus.
repeat rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite <- (Zpos_pos_of_Z _ _ He1).
ring.
caseEq (nat_of_P (pos_of_Z (e2 - e1))).
generalize (ZL4 (pos_of_Z (e2 - e1))).
intros (h, H0) H1. rewrite H0 in H1. discriminate H1.
simpl.
intros n H0.
apply nat_of_P_inj.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
apply sym_eq with (1 := H0).
split. exact He1.
split.
generalize (proj2 (Hg _) He1').
intros (H1,H2).
apply H2.
apply Zeq_le.
apply refl_equal.
split.
unfold shr.
rewrite iter_nat_of_P.
cut (Zpos (digits m1) <= e2 - e1)%Z. 2: omega.
intro H.
assert (nat_of_P (digits m1) <= nat_of_P (pos_of_Z (e2 - e1))).
apply not_gt.
intro H0.
elim Zgt_not_le with (2 := H).
rewrite (Zpos_pos_of_Z _ _ He1).
exact (nat_of_P_gt_Gt_compare_complement_morphism _ _ H0).
generalize (nat_of_P (pos_of_Z (e2 - e1))) m1 H0.
clear H0 H He1' He1 e2 e1 m1 Hg rexp.
assert (forall n : nat, forall b1 b2 : bool, forall m1 : positive,
  nat_of_P (digits m1) <= n ->
  rnd_m (iter_nat n rnd_record shr_aux (rnd_record_mk (Npos m1) b1 b2)) = N0).
induction n ; intros.
elim gt_not_le with (2 := H).
unfold gt.
apply lt_O_nat_of_P.
cutrewrite (S n = n + 1). 2: ring.
rewrite iter_nat_plus.
simpl.
unfold shr_aux at 2.
simpl.
caseEq m1 ; intros.
rewrite IHn.
apply refl_equal.
rewrite H0 in H.
unfold digits in H. fold digits in H.
rewrite nat_of_P_succ_morphism in H.
apply lt_n_Sm_le with (1 := H).
rewrite IHn.
apply refl_equal.
rewrite H0 in H.
unfold digits in H. fold digits in H.
rewrite nat_of_P_succ_morphism in H.
apply lt_n_Sm_le with (1 := H).
apply iter_nat_invariant.
2: apply refl_equal.
intros.
unfold shr_aux.
rewrite H1.
apply refl_equal.
intros n.
apply H.
apply Rlt_le_trans with (1 := proj2 (digits_float_correct m1 e1)).
unfold float2R.
simpl.
apply Rmult_le_compat_l.
auto with real.
cutrewrite (e2 = (e1 + Zpos (digits m1)) + (e2 - (e1 + Zpos (digits m1))))%Z.
2: ring.
rewrite (powerRZ_add 2%R (e1 + Zpos (digits m1))). 2: discrR.
pattern (powerRZ 2 (e1 + Zpos (digits m1))) at 1 ; rewrite <- Rmult_1_r.
apply Rmult_le_compat_l.
auto with real.
case (Zle_lt_or_eq _ _ He1') ; clear He1' ; intro He1' ; unfold powerRZ.
rewrite (Zpos_pos_of_Z _ _ He1').
auto with real.
rewrite He1'.
rewrite Zminus_diag.
apply Rle_refl.
Qed.

Lemma rexp_exclusive :
 forall rexp : Z -> Z,
 forall m1 m2 : positive, forall e1 e2 : Z,
 rexp (e1 + (Zpos (digits m1)))%Z = e1 ->
 rexp (e2 + (Zpos (digits m2)))%Z = e2 ->
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 Float2 (Zpos m2) e2 = Float2 (Zpos m1) e1 :>R.
intros rexp m1 m2 e1 e2 He1 He2 ([Hf1|Hf1],Hf2).
2: apply sym_eq with (1 := Hf1).
generalize (float2_repartition _ _ _ _ (conj Hf1 Hf2)).
intros (He3,He4).
rewrite <- He4 in He2.
rewrite He1 in He2.
rewrite He2.
cutrewrite (Zpos m2 = Zpos m1)%Z.
apply refl_equal.
omega.
Qed.

Lemma round_zr_bound :
 forall rexp : Z -> Z, good_rexp rexp ->
 forall m1 : positive, forall e1 : Z,
 let (m2,e2) := round_pos rndZR rexp m1 e1 in
 (Float2 (Z_of_N m2) e2 <= Float2 (Zpos m1) e1 < Float2 (Z_of_N m2 + 1) e2)%R.
intros rexp Hg m1 e1.
assert (HH: (Float2 (Z_of_N (Npos m1)) e1 <= Float2 (Zpos m1) e1
  < Float2 (Z_of_N (Npos m1) + 1) e1)%R).
split. apply Rle_refl.
apply float2_binade_lt.
exact (Zlt_succ (Zpos m1)).
generalize (rexp_case rexp Hg m1 e1).
intros [H|[(H,(H0,(H1,H2)))|(m3,(H,(H1,H2)))]].
rewrite round_rexp_exact. 2: exact H.
exact HH.
unfold round_pos.
rewrite (Zpos_pos_of_Z _ _ H).
simpl.
rewrite H1.
split. 2: apply H2.
unfold float2R.
simpl.
rewrite (Rmult_0_l).
apply Rmult_le_pos ; auto with real.
unfold round_pos, rndZR.
caseEq (rexp (e1 + Zpos (digits m1)) - e1)%Z ; intros.
exact HH.
rewrite H0 in H.
unfold pos_of_Z in H.
rewrite <- H.
exact H2.
exact HH.
Qed.

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

Lemma round_zero :
 forall rdir : round_dir,
 forall rexp : Z -> Z,
 forall e : Z,
 (round rdir rexp (Float2 Z0 e) = 0 :>R)%R.
intros rdir rexp e.
unfold round, float2R.
simpl.
auto with real.
Qed.

Lemma round_neg :
 forall rdir : round_dir,
 forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 round rdir rexp (Float2 (Zneg m) e) = Fopp2 (round
   (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir))
   rexp (Fopp2 (Float2 (Zneg m) e))).
intros rdir rexp m e.
unfold round, Fopp2.
simpl.
case (round_pos (rneg rdir) rexp m e) ; intros.
case n ; trivial.
Qed.

Axiom round_extension :
 forall rdir : round_dir, forall rexp : Z -> Z,
 good_rexp rexp ->
 sigT (fun fext : R -> R =>
 (forall x y : R, (fext x <= fext y)%R) /\
 (forall f : float2, fext f = round rdir rexp f) /\
 (forall x : R, forall k : Z,
  (powerRZ 2 (k - 1) <= Rabs x < powerRZ 2 k)%R ->
  exists f : float2, fext x = f /\ Fexp f = rexp k) /\
 (forall x : R, exists f1 : float2, exists f2 : float2,
  (f1 <= x <= f2)%R /\ fext x = fext f1 /\ fext x = fext f2)).

End Gappa_round.
