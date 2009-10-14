Require Import Decidable.
Require Import Bool.
Require Import ZArith.
Require Import Reals.
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

Lemma round_constant_xO :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 good_rdir rdir ->
 tofloat (round_pos rdir rexp m e) = tofloat (round_pos rdir rexp (xO m) (e - 1)) :>R.
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

Lemma round_unicity_aux :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m1 m2 : positive, forall e1 e2 : Z,
 good_rdir rdir -> (e1 < e2)%Z ->
 Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R ->
 tofloat (round_pos rdir rexp m1 e1) = tofloat (round_pos rdir rexp m2 e2) :>R.
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
generalize (float2_binade_eq_reg _ _ _ H).
intro H0. injection H0. intro H1. rewrite H1.
exact (refl_equal _).
intros m1 Heq.
cut (exists p, m1 = xO p).
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
cutrewrite (Zpos (xO p) = Zpos p * 2)%Z.
apply float2_shift_m1.
rewrite Zmult_comm.
apply refl_equal.
clear IHn Hdir rexp rdir.
rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ in Heq.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P in Heq.
rewrite <- (float2_shl_correct (Zpos m2) e2 (P_of_succ_nat n)) in Heq.
simpl in Heq.
generalize (float2_binade_eq_reg _ _ _ Heq).
intro H0. injection H0. intro H1. rewrite H1.
rewrite shift_pos_nat.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
exists (shift_nat n m2).
exact (refl_equal _).
Qed.

Lemma round_unicity :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 forall m1 m2 : positive, forall e1 e2 : Z,
 good_rdir rdir ->
 Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R ->
 tofloat (round_pos rdir rexp m1 e1) = tofloat (round_pos rdir rexp m2 e2) :>R.
intros rdir rexp m1 m2 e1 e2 Hdir Heq.
case (Ztrichotomy e1 e2) ; [ intros H | intros [H|H] ].
apply round_unicity_aux with (1 := Hdir) (2 := H) (3 := Heq).
rewrite H in Heq.
generalize (float2_binade_eq_reg _ _ _ Heq).
intro H0. injection H0. intro H1. rewrite H1.
rewrite H.
exact (refl_equal _).
apply sym_eq.
apply round_unicity_aux with (1 := Hdir).
auto with zarith.
rewrite Heq.
exact (refl_equal _).
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
 (tofloat (round_pos rdir rexp m2 e2) <= tofloat (round_pos rdir rexp m3 e3))%R.
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
apply Rle_refl.
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
unfold tofloat.
apply float2_binade_le.
case (rdir (rnd_record_mk (Npos m1) false true)) ; simpl ;
try rewrite Zpos_succ_morphism ; auto with zarith.
rewrite (proj1 Hc2 H2).
rewrite (proj1 Hc3 H3).
unfold tofloat.
apply float2_binade_le.
auto with zarith.
elim Rle_not_lt with (1 := Hf).
apply Rlt_le_trans with (1 := proj2 H3).
generalize H2. clear H2. intros [H2|H2].
rewrite H2.
apply Rle_refl.
apply Rlt_le with (1 := proj1 H2).
(* *)
intros [H2|[H2|[H2|H2]]].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_rexp_exact rdir rexp m1 e1).
rewrite (proj1 (proj2 Hc3) H3).
unfold tofloat.
apply float2_binade_le.
case (rdir (rnd_record_mk (Npos m1) true false) e1) ; simpl ;
try rewrite Zpos_succ_morphism ; auto with zarith.
apply Zeq_le with (1 := He1).
rewrite (proj1 Hc2 H2).
rewrite (proj1 (proj2 Hc3) H3).
unfold tofloat.
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
apply Rle_refl.
elim Rle_not_lt with (1 := Hf).
rewrite H3.
exact (proj1 H2).
(* *)
rewrite (proj2 (proj2 Hc3) H3).
intros [H2|[H2|[H2|H2]]].
rewrite (round_unicity rdir rexp m2 m1 e2 e1 Hgd H2).
rewrite (round_rexp_exact rdir rexp m1 e1).
unfold tofloat.
apply float2_binade_le.
case (rdir (rnd_record_mk (Npos m1) true true)) ;
simpl ; try rewrite Zpos_succ_morphism ; auto with zarith.
apply Zeq_le with (1 := He1).
rewrite (proj1 Hc2 H2).
unfold tofloat.
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
unfold tofloat.
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
apply Rle_refl.
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

Lemma round_monotone_underflow :
 forall rdir : rnd_record -> Z -> bool,
 forall rexp : Z -> Z,
 good_rdir rdir ->
 good_rexp rexp ->
 forall k : Z,
 rexp k = k ->
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 <= Float2 1 k)%R ->
 (Float2 (Zpos m2) e2 <= Float2 1 k)%R ->
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2)%R ->
 (tofloat (round_pos rdir rexp m1 e1) <= tofloat (round_pos rdir rexp m2 e2))%R.
intros rdir rexp Hgd Hge e1 He1 m2 m3 e2 e3 [Hb2|Hb2] [Hb3|Hb3] Hf.
generalize (round_constant_underflow rdir _ Hge _ He1 m3 e3).
generalize (round_constant_underflow rdir _ Hge _ He1 m2 e2).
intros Hc2 Hc3.
generalize (bracket_case_underflow m2 e2 e1 Hb2).
generalize (bracket_case_underflow m3 e3 e1 Hb3).
intros [H3|[H3|H3]].
(* *)
intros [H2|H2].
rewrite (proj1 Hc2 H2).
rewrite (proj1 Hc3 H3).
unfold tofloat.
apply float2_binade_le.
auto with zarith.
elim Rle_not_lt with (1 := Hf).
apply Rlt_le_trans with (1 := H3).
generalize H2. clear H2. intros [H2|H2].
rewrite H2.
apply Rle_refl.
apply Rlt_le with (1 := proj1 H2).
(* *)
intros [H2|[H2|H2]].
rewrite (proj1 Hc2 H2).
rewrite (proj1 (proj2 Hc3) H3).
unfold tofloat.
apply float2_binade_le.
caseEq (rdir (rnd_record_mk 0 false true) e1) ;
caseEq (rdir (rnd_record_mk 0 true false) e1) ;
intros H4 H5 ; simpl ; try rewrite Zpos_succ_morphism ;
auto with zarith ; generalize (Hgd N0 e1).
intros (_,([H6|H6],_)).
rewrite H6 in H5.
discriminate H5.
rewrite H6 in H4.
discriminate H4.
rewrite (proj1 (proj2 Hc2) H2).
rewrite (proj1 (proj2 Hc3) H3).
apply Rle_refl.
elim Rle_not_lt with (1 := Hf).
rewrite H3.
exact (proj1 H2).
(* *)
rewrite (proj2 (proj2 Hc3) H3).
intros [H2|[H2|H2]].
rewrite (proj1 Hc2 H2).
unfold tofloat.
apply float2_binade_le.
caseEq (rdir (rnd_record_mk N0 false true) e1) ;
caseEq (rdir (rnd_record_mk N0 true true) e1) ;
intros H4 H5 ; simpl ; try rewrite Zpos_succ_morphism ;
auto with zarith ; generalize (Hgd N0 e1).
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
unfold tofloat.
apply float2_binade_le.
caseEq (rdir (rnd_record_mk N0 true false) e1) ;
caseEq (rdir (rnd_record_mk N0 true true) e1) ;
intros H4 H5 ; simpl ; try rewrite Zpos_succ_morphism ;
auto with zarith ; generalize (Hgd N0 e1).
intros (_,(_,[H6|H6])).
rewrite H6 in H5.
discriminate H5.
rewrite H6 in H4.
discriminate H4.
rewrite (proj2 (proj2 Hc2) H2).
apply Rle_refl.
(* *)
assert (rexp (e1 + Zpos (digits 1)) <= e1)%Z.
simpl.
generalize (proj1 (proj2 (Hge _) (Zeq_le _ _ (sym_eq He1)))).
rewrite He1.
trivial.
rewrite (round_unicity rdir rexp m3 xH e3 e1 Hgd Hb3).
rewrite (round_rexp_exact rdir rexp xH e1 H).
generalize (round_constant_underflow rdir _ Hge _ He1 m2 e2).
intros Hc2.
generalize (bracket_case_underflow m2 e2 e1 Hb2).
assert (H4: (Float2 0 e1 <= Float2 1 e1)%R).
apply float2_binade_le.
auto with zarith.
intros [H2|[H2|H2]].
rewrite (proj1 Hc2 H2).
case (rdir (rnd_record_mk N0 false true)).
apply Rle_refl.
exact H4.
rewrite (proj1 (proj2 Hc2) H2).
case (rdir (rnd_record_mk N0 true false)).
apply Rle_refl.
exact H4.
rewrite (proj2 (proj2 Hc2) H2).
case (rdir (rnd_record_mk N0 true true)).
apply Rle_refl.
exact H4.
(* *)
elim Rle_not_lt with (1 := Hf).
rewrite Hb2.
exact Hb3.
(* *)
apply Req_le.
apply round_unicity with (1 := Hgd).
rewrite Hb3.
exact Hb2.
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

Lemma rexp_case :
 forall rexp : Z -> Z, good_rexp rexp ->
 forall m1 : positive, forall e1 : Z,
 let e2 := rexp (e1 + Zpos (digits m1))%Z in
 (e2 <= e1)%Z \/
 ((e1 + Zpos (digits m1) <= e2)%Z /\ rexp e2 = e2 /\
  rnd_m (shr m1 (pos_of_Z (e2 - e1))) = N0 /\
  (Float2 (Zpos m1) e1 < Float2 1 e2)%R) \/
 ((e1 < e2 < e1 + Zpos (digits m1))%Z /\
  exists m2 : positive,
  Npos m2 = rnd_m (shr m1 (pos_of_Z (e2 - e1))) /\
  rexp (e2 + Zpos (digits m2))%Z = e2 /\
  (Float2 (Zpos m2) e2 <= Float2 (Zpos m1) e1 < Float2 (Zpos m2 + 1) e2)%R).
intros rexp Hg m1 e1 e2.
case (Z_lt_le_dec e1 e2) ; intro He1 ; [ right | left ].
2: exact He1.
case (Z_lt_le_dec e2 (e1 + Zpos (digits m1))%Z) ; intro He1' ; [ right | left ].
cut (e2 - e1 < Zpos (digits m1))%Z. 2: omega.
rewrite <- (Zpos_pos_of_Z_minus _ _ He1).
intro H.
generalize (nat_of_P_lt_Lt_compare_morphism _ _ H).
clear H. intro H.
generalize (rexp_case_aux m1 e1 (nat_of_P (pos_of_Z (e2 - e1))) H).
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
rewrite (Zpos_pos_of_Z_minus _ _ He1).
cutrewrite (e1 + (e2 - e1) = e2)%Z. 2: ring.
clear H. intros (m2,H).
split.
exact (conj He1 He1').
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
rewrite (Zpos_pos_of_Z_minus _ _ He1).
ring.
split. exact He1'.
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
rewrite <- (Zpos_pos_of_Z_minus _ _ He1).
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
apply Rlt_le_trans with (1 := proj2 (float2_digits_correct m1 e1)).
apply float2_Rle_pow2 with (1 := He1').
Qed.

Lemma rexp_exclusive :
 forall rexp : Z -> Z,
 forall m1 m2 : positive, forall e1 e2 : Z,
 rexp (e1 + (Zpos (digits m1)))%Z = e1 ->
 rexp (e2 + (Zpos (digits m2)))%Z = e2 ->
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2 < Float2 (Zpos m1 + 1) e1)%R ->
 Float2 (Zpos m2) e2 = Float2 (Zpos m1) e1.
intros rexp m1 m2 e1 e2 He1 He2 ([Hf1|Hf1],Hf2).
generalize (float2_repartition _ _ _ _ (conj Hf1 Hf2)).
intros (He3,He4).
elim Zlt_not_eq with (1 := He3).
rewrite <- He2.
rewrite <- He4.
exact He1.
clear Hf2.
cutrewrite (e2 + Zpos (digits m2) = e1 + Zpos (digits m1))%Z in He2.
rewrite He1 in He2.
rewrite He2 in Hf1.
rewrite He2.
rewrite (float2_binade_eq_reg _ _ _ Hf1).
exact (refl_equal _).
apply Zle_antisym ; apply Znot_gt_le ; intro.
apply Rlt_not_eq with (2 := Hf1).
apply Rlt_le_trans with (1 := proj2 (float2_digits_correct m1 e1)).
apply Rle_trans with (2 := proj1 (float2_digits_correct m2 e2)).
apply float2_Rle_pow2.
omega.
apply Rlt_not_eq with (2 := sym_eq Hf1).
apply Rlt_le_trans with (1 := proj2 (float2_digits_correct m2 e2)).
apply Rle_trans with (2 := proj1 (float2_digits_correct m1 e1)).
apply float2_Rle_pow2.
omega.
Qed.

Lemma round_canonic :
 forall rexp : Z -> Z,
 forall m1 : positive, forall e1 : Z,
 (rexp (e1 + Zpos (digits m1)) <= e1)%Z ->
 exists m2 : positive, exists e2 : Z,
 Float2 (Zpos m1) e1 = Float2 (Zpos m2) e2 :>R /\
 rexp (e2 + Zpos (digits m2))%Z = e2.
intros rexp m1 e1 He.
induction (Zle_lt_or_eq _ _ He) ; clear He ; rename H into He.
rewrite <- (float2_shl_correct (Zpos m1) e1 (pos_of_Z (e1 - rexp (e1 + Zpos (digits m1)))%Z)).
simpl.
rewrite (Zpos_pos_of_Z_minus _ _ He).
cutrewrite (e1 - (e1 - rexp (e1 + Zpos (digits m1))) = rexp (e1 + Zpos (digits m1)))%Z. 2: ring.
exists (shift_pos (pos_of_Z (e1 - rexp (e1 + Zpos (digits m1))%Z)) m1).
exists (rexp (e1 + Zpos (digits m1))%Z).
split. apply refl_equal.
apply (f_equal rexp).
cutrewrite (Zpos (digits (shift_pos (pos_of_Z (e1 - rexp (e1 + Zpos (digits m1)))) m1)) = Zpos (digits m1) + Zpos (pos_of_Z (e1 - rexp (e1 + Zpos (digits m1)))))%Z.
rewrite (Zpos_pos_of_Z_minus _ _ He).
ring.
rewrite shift_pos_nat.
set (d := pos_of_Z (e1 - rexp (e1 + Zpos (digits m1))%Z)).
rewrite (Zpos_eq_Z_of_nat_o_nat_of_P d).
induction (nat_of_P d).
rewrite Zplus_0_r.
apply refl_equal.
rewrite inj_S.
simpl (digits (shift_nat (S n) m1)).
rewrite Zpos_succ_morphism.
fold (shift_nat n m1).
rewrite IHn.
unfold Zsucc.
ring.
exists m1. exists e1.
rewrite He.
split ; apply refl_equal.
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

Lemma round_bound_underflow :
 forall rdir : rnd_record -> Z -> bool, forall rexp : Z -> Z,
 good_rexp rexp ->
 forall k : Z, rexp k = k ->
 forall m : positive, forall e : Z,
 (Float2 (Zpos m) e < Float2 1 k)%R ->
 (tofloat (round_pos rdir rexp m e) <= Float2 1 k)%R.
intros rdir rexp Hg k Hk m e Hb.
assert (H0: forall b1 b2 : bool, (tofloat
  (if rdir (rnd_record_mk 0 b1 b2) k then 1%N
  else 0%N, k) <= Float2 1 k)%R).
intros b1 b2.
case (rdir (rnd_record_mk 0 b1 b2) k).
apply Rle_refl.
simpl.
apply float2_binade_le.
auto with zarith.
generalize (round_constant_underflow rdir rexp Hg k Hk m e).
intros (Hc1,(Hc2,Hc3)).
generalize (bracket_case_underflow m e k Hb).
intros [H|[H|H]].
rewrite (Hc1 H).
apply H0.
rewrite (Hc2 H).
apply H0.
rewrite (Hc3 H).
apply H0.
Qed.

Lemma round_monotone :
 forall rdir : rnd_record -> Z -> bool,
 forall rexp : Z -> Z,
 good_rdir rdir ->
 good_rexp rexp ->
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2)%R ->
 (tofloat (round_pos rdir rexp m1 e1) <= tofloat (round_pos rdir rexp m2 e2))%R.
intros rdir rexp Hgd Hge m1 m2 e1 e2 Hf.
generalize (rexp_case rexp Hge m2 e2).
generalize (rexp_case rexp Hge m1 e1).
intros [H1a|[(H1a,(H1b,(H1c,H1d)))|(_,(m3,(H1a,(H1b,H1c))))]]
       [H2a|[(H2a,(H2b,(H2c,H2d)))|(_,(m4,(H2a,(H2b,H2c))))]].
(* *)
rewrite (round_rexp_exact rdir _ _ _ H1a).
rewrite (round_rexp_exact rdir _ _ _ H2a).
exact Hf.
(* *)
elim Rlt_not_le with (2 := Hf).
apply Rlt_le_trans with (1 := H2d).
apply Rle_trans with (2 := proj1 (float2_digits_correct m1 e1)).
apply float2_Rle_pow2.
clear Hf H2c H2d.
generalize (proj2 (proj2 (Hge _) (Zeq_le _ _ (sym_eq H2b))) (e1 + Zpos (digits m1))%Z).
generalize (Zgt_pos_0 (digits m1)).
omega.
(* *)
rewrite (round_rexp_exact rdir _ _ _ H1a).
apply Rle_trans with (2 := proj1 (round_bound_local _ _ Hgd _ _ H2b _ _ H2c)).
generalize (round_canonic _ _ _ H1a).
intros (m3,(e3,(H1b,H1c))).
simpl. rewrite H1b.
case (Rle_or_lt (Float2 (Zpos m4 + 1) (rexp (e2 + Zpos (digits m2))%Z)) (Float2 (Zpos m3) e3)) ; intros H.
elim Rle_not_lt with (1 := H).
rewrite <- H1b.
apply Rle_lt_trans with (1 := Hf).
exact (proj2 H2c).
apply Rnot_lt_le.
intro H0.
apply Rlt_not_eq with (1 := H0).
apply sym_eq.
rewrite (rexp_exclusive rexp _ _ _ _ H2b H1c (conj (Rlt_le _ _ H0) H)).
apply refl_equal.
(* *)
apply Rle_trans with (1 := round_bound_underflow rdir _ Hge _ H1b _ _ H1d).
rewrite (round_rexp_exact rdir _ _ _ H2a).
apply Rle_trans with (2 := proj1 (float2_digits_correct m2 e2)).
apply float2_Rle_pow2.
clear Hf H1c H1d.
generalize (proj2 (proj2 (Hge _) (Zeq_le _ _ (sym_eq H1b))) (e2 + Zpos (digits m2))%Z).
generalize (Zgt_pos_0 (digits m2)).
omega.
(* *)
cutrewrite (rexp (e2 + Zpos (digits m2)) = rexp (e1 + Zpos (digits m1)))%Z in H2d.
exact (round_monotone_underflow _ _ Hgd Hge _ H1b _ _ _ _ (Rlt_le _ _ H1d) (Rlt_le _ _ H2d) Hf).
generalize (proj2 (proj2 (Hge _) (Zeq_le _ _ (sym_eq H2b))) (e1 + Zpos (digits m1))%Z).
generalize (proj2 (proj2 (Hge _) (Zeq_le _ _ (sym_eq H1b))) (e2 + Zpos (digits m2))%Z).
generalize (Zgt_pos_0 (digits m1)) (Zgt_pos_0 (digits m2)).
clear Hf H1c H1d H2c H2d.
omega.
(* *)
apply Rle_trans with (1 := round_bound_underflow rdir _ Hge _ H1b _ _ H1d).
apply Rle_trans with (2 := proj1 (round_bound_local _ _ Hgd _ _ H2b _ _ H2c)).
apply Rle_trans with (2 := proj1 (float2_digits_correct m4 (rexp (e2 + Zpos (digits m2))%Z))).
apply float2_Rle_pow2.
clear Hf H1c H1d H2c.
generalize (proj2 (proj2 (Hge _) (Zeq_le _ _ (sym_eq H1b))) (rexp (e2 + Zpos (digits m2)) + Zpos (digits m4))%Z).
generalize (Zgt_pos_0 (digits m4)).
omega.
(* *)
elim Hf ; clear Hf ; intro Hf.
rewrite (round_rexp_exact rdir _ _ _ H2a).
apply Rle_trans with (1 := proj2 (round_bound_local _ _ Hgd _ _ H1b _ _ H1c)).
generalize (round_canonic _ _ _ H2a).
intros (m4,(e4,(H2b,H2c))).
apply Rnot_lt_le.
generalize (Rle_lt_trans _ _ _ (proj1 H1c) Hf).
simpl.
rewrite H2b.
intros H0 H1.
apply Rlt_not_eq with (1 := H0).
apply sym_eq.
rewrite (rexp_exclusive rexp _ _ _ _ H1b H2c (conj (Rlt_le _ _ H0) H1)).
apply refl_equal.
apply Req_le.
apply round_unicity with (1 := Hgd) (2 := Hf).
(* *)
elim Rlt_not_le with (2 := Hf).
apply Rlt_le_trans with (1 := H2d).
apply Rle_trans with (2 := proj1 H1c).
apply Rle_trans with (2 := proj1 (float2_digits_correct m3 (rexp (e1 + Zpos (digits m1))%Z))).
apply float2_Rle_pow2.
clear Hf H1a H1c H2c H2d.
generalize (proj2 (proj2 (Hge _) (Zeq_le _ _ (sym_eq H2b))) (rexp (e1 + Zpos (digits m1)) + Zpos (digits m3))%Z).
generalize (Zgt_pos_0 (digits m1)) (Zgt_pos_0 (digits m3)).
omega.
(* *)
case (Rle_or_lt (Float2 (Zpos m3 + 1) (rexp (e1 + Zpos (digits m1))%Z)) (Float2 (Zpos m4) (rexp (e2 + Zpos (digits m2))%Z))) ; intros H.
apply Rle_trans with (1 := proj2 (round_bound_local _ _ Hgd _ _ H1b _ _ H1c)).
apply Rle_trans with (2 := proj1 (round_bound_local _ _ Hgd _ _ H2b _ _ H2c)).
exact H.
case (Rle_or_lt (Float2 (Zpos m3) (rexp (e1 + Zpos (digits m1))%Z)) (Float2 (Zpos m4) (rexp (e2 + Zpos (digits m2))%Z))) ; intros H0.
generalize (rexp_exclusive rexp _ _ _ _ H1b H2b (conj H0 H)).
intro H1.
injection H1.
intros H2 H3.
rewrite H2 in H2c.
rewrite H3 in H2c.
clear H1 H2 H3.
exact (round_monotone_local _ _ Hgd Hge _ _ H1b _ _ _ _
  (conj (proj1 H1c) (Rlt_le _ _ (proj2 H1c))) (conj (proj1 H2c) (Rlt_le _ _ (proj2 H2c))) Hf).
case (Rle_or_lt (Float2 (Zpos m4 + 1) (rexp (e2 + Zpos (digits m2))%Z)) (Float2 (Zpos m3) (rexp (e1 + Zpos (digits m1))%Z))) ; intros H1.
elim Rlt_not_le with (2 := Hf).
apply Rlt_le_trans with (2 := proj1 H1c).
apply Rlt_le_trans with (1 := proj2 H2c).
exact H1.
generalize (rexp_exclusive rexp _ _ _ _ H2b H1b (conj (Rlt_le _ _ H0) H1)).
intro H2.
injection H2.
intros H3 H4.
rewrite H3 in H1c.
rewrite H4 in H1c.
clear H2 H3 H4.
exact (round_monotone_local _ _ Hgd Hge _ _ H2b _ _ _ _
  (conj (proj1 H1c) (Rlt_le _ _ (proj2 H1c))) (conj (proj1 H2c) (Rlt_le _ _ (proj2 H2c))) Hf).
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

Lemma log2 :
  forall x : R, (0 < x)%R ->
  { k : Z | (powerRZ 2 (k - 1) <= x < powerRZ 2 k)%R }.
Proof.
intros x Hx.
(* . *)
assert (Hr: (0 < ln 2)%R).
apply exp_lt_inv.
rewrite exp_0.
rewrite exp_ln.
now apply (Z2R_lt 1 2).
now apply (Z2R_lt 0 2).
(* . *)
assert (He: forall e, powerRZ 2 e = exp (Z2R e * ln 2)).
clear -Hr.
(* .. *)
assert (forall e, powerRZ 2 (Zpos e) = exp (Z2R (Zpos e) * ln 2)).
intros e.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
change 2%R with (INR 2).
rewrite <- Zpower_nat_powerRZ.
rewrite Z2R_IZR.
induction (nat_of_P e).
rewrite Rmult_0_l.
unfold Zpower_nat, iter_nat.
now rewrite exp_0.
change (S n) with (1 + n)%nat.
rewrite Zpower_nat_is_exp.
rewrite mult_IZR, IHn.
rewrite <- 2!INR_IZR_INZ, plus_INR.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite exp_plus.
rewrite exp_ln.
apply refl_equal.
now apply (Z2R_lt 0 2).
(* .. *)
intros [|e|e].
rewrite Rmult_0_l.
now rewrite exp_0.
apply H.
change (Z2R (Zneg e)) with (-Z2R (Zpos e))%R.
rewrite Ropp_mult_distr_l_reverse.
rewrite exp_Ropp.
now rewrite <- H.
(* . *)
exists (up (ln x / ln 2)).
rewrite 2!He.
pattern x at 2 3 ; replace x with (exp (ln x * / ln 2 * ln 2)).
split.
rewrite minus_Z2R.
cut ((Z2R (up (ln x * / ln 2)) - Z2R 1) * ln 2 <= ln x * / ln 2 * ln 2)%R.
intros [H|H].
left. now apply exp_increasing.
right. now apply f_equal.
apply Rmult_le_compat_r.
now apply Rlt_le.
apply Rplus_le_reg_l with (1 - ln x * / ln 2)%R.
simpl (Z2R 1).
replace (1 - ln x * / ln 2 + ln x * / ln 2)%R with R1 by ring.
replace (1 - ln x * / ln 2 + (Z2R (up (ln x * / ln 2)) - 1))%R with (Z2R (up (ln x * / ln 2)) - ln x * / ln 2)%R by ring.
rewrite Z2R_IZR.
exact (proj2 (archimed _)).
apply exp_increasing.
apply Rmult_lt_compat_r.
exact Hr.
rewrite Z2R_IZR.
exact (proj1 (archimed _)).
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
now apply exp_ln.
now apply Rgt_not_eq.
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

Lemma round_extension_prop_zero :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge :good_rexp rexp,
 round_extension rdir rexp Hge 0 = Float2 0 0.
intros rdir rexp Hge.
unfold round_extension.
generalize (total_order_T 0 0).
intros [[H|H]|H].
elim (Rlt_irrefl _ H).
apply refl_equal.
elim (Rlt_irrefl _ H).
Qed.

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

Lemma round_extension_float2 :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall f : float2,
 round_extension rdir rexp Hge f = round rdir rexp f :>R.
intros rdir rexp Hge f.
cutrewrite (f = Float2 (Fnum f) (Fexp f)).
2: induction f ; apply refl_equal.
case (Fnum f) ; intros.
rewrite float2_zero.
rewrite round_extension_prop_zero.
apply refl_equal.
assert (0 < Float2 (Zpos p) (Fexp f))%R.
apply float2_pos_compat.
split.
generalize (round_extension_prop_pos rdir rexp Hge _ H).
intros (m1,(m2,(e1,(e2,(H1,(H2,(H3,_))))))).
apply Rle_antisym.
rewrite H2.
unfold round. simpl.
repeat rewrite tofloat_0.
apply (round_monotone _ _ (rpos_good rdir) Hge).
exact (proj1 H1).
rewrite H3.
unfold round. simpl.
repeat rewrite tofloat_0.
apply (round_monotone _ _ (rpos_good rdir) Hge).
exact (proj2 H1).
assert (0 > Float2 (Zneg p) (Fexp f))%R.
change (0 > Fopp2 (Float2 (Zpos p) (Fexp f)))%R.
rewrite Fopp2_correct.
apply Ropp_0_lt_gt_contravar.
apply float2_pos_compat.
split.
generalize (round_extension_prop_neg rdir rexp Hge _ H).
intros (m1,(m2,(e1,(e2,(H1,(H2,(H3,_))))))).
cutrewrite (round rdir rexp (Float2 (Zneg p) (Fexp f)) = -round
  (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir)) rexp (Float2 (Zpos p) (Fexp f)) :>R)%R.
rewrite <- Fopp2_correct in H1.
unfold Fopp2 in H1. simpl in H1.
apply Rle_antisym.
rewrite H3.
rewrite Fopp2_correct.
apply Ropp_le_contravar.
unfold round. simpl.
repeat rewrite tofloat_0.
apply (round_monotone _ _ (rneg_good rdir) Hge).
exact (proj2 H1).
rewrite H2.
rewrite Fopp2_correct.
apply Ropp_le_contravar.
unfold round. simpl.
repeat rewrite tofloat_0.
apply (round_monotone _ _ (rneg_good rdir) Hge).
exact (proj1 H1).
rewrite <- Fopp2_correct.
unfold round. simpl.
case (round_pos (rneg rdir) rexp p (Fexp f)) ; intros.
case n ; intros ; apply refl_equal.
Qed.

Lemma round_extension_zero :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 round_extension rdir rexp Hge 0 = R0 :>R.
intros rdir rexp Hge.
rewrite round_extension_prop_zero.
apply refl_equal.
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
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x y : R, (x <= y)%R ->
 (round_extension rdir rexp Hge x <= round_extension rdir rexp Hge y)%R.
intros rdir rexp Hge x y H.
generalize (total_order_T 0 x).
intros [[Hx|Hx]|Hx].
generalize (total_order_T 0 y).
intros [[Hy|Hy]|Hy].
generalize (round_extension_prop_pos rdir rexp Hge _ Hx).
intros (mx1,(mx2,(ex1,(ex2,(Hx1,(Hx2,(Hx3,_))))))).
generalize (round_extension_prop_pos rdir rexp Hge _ Hy).
intros (my1,(my2,(ey1,(ey2,(Hy1,(Hy2,(Hy3,_))))))).
rewrite Hx2. rewrite Hy3.
unfold round. simpl.
repeat rewrite tofloat_0.
apply (round_monotone _ _ (rpos_good rdir) Hge).
apply Rle_trans with (1 := proj1 Hx1).
exact (Rle_trans _ _ _ H (proj2 Hy1)).
rewrite <- Hy in H.
elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ Hx H)).
elim (Rlt_not_le _ _ (Rlt_trans _ _ _ Hy Hx) H).
rewrite <- Hx.
rewrite round_extension_zero.
rewrite <- Hx in H.
unfold Rle in H.
decompose [or] H.
apply round_extension_positive.
exact H0.
rewrite <- H0.
rewrite round_extension_zero.
apply Rle_refl.
generalize (total_order_T 0 y).
intros [[Hy|Hy]|Hy].
apply Rle_trans with R0.
apply round_extension_negative.
exact Hx.
apply round_extension_positive.
exact Hy.
rewrite <- Hy.
rewrite round_extension_zero.
apply round_extension_negative.
exact Hx.
generalize (round_extension_prop_neg rdir rexp Hge _ Hx).
intros (mx1,(mx2,(ex1,(ex2,(Hx1,(Hx2,(Hx3,_))))))).
generalize (round_extension_prop_neg rdir rexp Hge _ Hy).
intros (my1,(my2,(ey1,(ey2,(Hy1,(Hy2,(Hy3,_))))))).
rewrite Hx3. rewrite Hy2.
unfold round. simpl.
repeat rewrite Fopp2_correct.
apply Ropp_le_contravar.
repeat rewrite tofloat_0.
apply (round_monotone _ _ (rneg_good rdir) Hge).
apply Rle_trans with (1 := proj1 Hy1).
apply Rle_trans with (2 := proj2 Hx1).
apply Ropp_le_contravar.
exact H.
Qed.

Lemma round_extension_opp :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp, forall x : R,
 (round_extension rdir rexp Hge (-x) = - round_extension
  (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir))
  rexp Hge x :>R)%R.
intros rdir rexp Hge x.
destruct (total_order_T 0 x) as [[H|H]|H9] ; simpl.
(* *)
destruct (round_extension_prop_pos (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir)) _ Hge _ H) as (m1,(m2,(e1,(e2,(H1,(H2,(H3,_))))))).
apply Rle_antisym.
assert (-x <= Float2 (Zneg m1) e1)%R.
rewrite <- (Ropp_involutive (Float2 (Zneg m1) e1)).
rewrite <- Fopp2_correct.
unfold Fopp2. simpl.
apply Ropp_le_contravar with (1 := proj1 H1).
apply Rle_trans with (1 := round_extension_monotone rdir _ Hge _ _ H0).
rewrite round_extension_float2.
rewrite round_neg.
rewrite Fopp2_correct.
apply Ropp_le_contravar.
rewrite H2.
apply Rle_refl.
assert (Float2 (Zneg m2) e2 <= -x)%R.
rewrite <- (Ropp_involutive (Float2 (Zneg m2) e2)).
rewrite <- Fopp2_correct.
unfold Fopp2. simpl.
apply Ropp_le_contravar with (1 := proj2 H1).
apply Rle_trans with (2 := round_extension_monotone rdir _ Hge _ _ H0).
rewrite round_extension_float2.
rewrite round_neg.
rewrite Fopp2_correct.
apply Ropp_le_contravar.
rewrite H3.
apply Rle_refl.
(* *)
rewrite <- H.
rewrite Ropp_0.
repeat rewrite round_extension_zero.
exact (sym_eq Ropp_0).
(* *)
assert (0 < -x)%R.
apply Ropp_0_gt_lt_contravar with (1 := H9).
destruct (round_extension_prop_pos rdir _ Hge _ H) as (m1,(m2,(e1,(e2,(H1,(H2,(H3,_))))))).
simpl in H2, H3.
rewrite <- (Ropp_involutive (round_extension rdir rexp Hge (-x))).
apply Rle_antisym.
assert (x <= Float2 (Zneg m1) e1)%R.
rewrite <- (Ropp_involutive (Float2 (Zneg m1) e1)).
rewrite <- Fopp2_correct.
unfold Fopp2. simpl.
rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar with (1 := proj1 H1).
apply Ropp_le_contravar.
apply Rle_trans with (1 := round_extension_monotone (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir)) _ Hge _ _ H0).
rewrite round_extension_float2.
rewrite round_neg. simpl.
rewrite Fopp2_correct.
apply Ropp_le_contravar.
rewrite H2.
apply Rle_refl.
assert (Float2 (Zneg m2) e2 <= x)%R.
rewrite <- (Ropp_involutive (Float2 (Zneg m2) e2)).
rewrite <- Fopp2_correct.
unfold Fopp2. simpl.
rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar with (1 := proj2 H1).
apply Ropp_le_contravar.
apply Rle_trans with (2 := round_extension_monotone (round_dir_mk (rneg rdir) (rpos rdir) (rneg_good rdir) (rpos_good rdir)) _ Hge _ _ H0).
rewrite round_extension_float2.
rewrite round_neg. simpl.
rewrite Fopp2_correct.
apply Ropp_le_contravar.
rewrite H3.
apply Rle_refl.
Qed.

Definition rexp_representable (rexp : Z -> Z) (m e : Z) :=
 match m with
 | Z0 => True
 | Zpos p => (rexp (e + Zpos (digits p)) <= e)%Z
 | Zneg p => (rexp (e + Zpos (digits p)) <= e)%Z
 end.

Lemma round_extension_representable :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall f : float2,
 rexp_representable rexp (Fnum f) (Fexp f) ->
 round_extension rdir rexp Hge f = f :>R.
intros rdir rexp Hge f Hr.
rewrite round_extension_float2.
cutrewrite (f = Float2 (Fnum f) (Fexp f)).
unfold round.
induction (Fnum f) ; intros ; simpl.
repeat rewrite float2_zero.
exact (refl_equal _).
rewrite (round_rexp_exact (rpos rdir) _ _ _ Hr).
apply refl_equal.
rewrite (round_rexp_exact (rneg rdir) _ _ _ Hr).
apply refl_equal.
induction f ; apply refl_equal.
Qed.

Lemma representable_round_pos :
 forall rdir : rnd_record -> Z -> bool, good_rdir rdir ->
 forall rexp : Z -> Z, good_rexp rexp ->
 forall m : positive, forall e : Z,
 match round_pos rdir rexp m e with
 | (Npos p, q) =>
   exists r : positive, exists s : Z,
   Float2 (Zpos p) q = Float2 (Zpos r) s :>R /\
   (rexp(s + Zpos (digits r)) <= s)%Z
 | _ => True
 end.
intros rdir Hgd rexp Hge m e.
destruct (rexp_case _ Hge m e) as [Ha|[(Ha,(Hb,(Hc,Hd)))|((Hd,He),(n,(Ha,(Hb,Hc))))]].
rewrite (round_rexp_exact rdir _ _ _ Ha).
exists m. exists e.
split.
exact (refl_equal _).
exact Ha.
assert (forall b : bool,
  match (if b then 1%N else 0%N) with
  | 0%N => True
  | Npos p => exists r : positive, exists s : Z,
    Float2 (Zpos p) (rexp (e + Zpos (digits m))%Z) = Float2 (Zpos r) s :>R
    /\ (rexp (s + Zpos (digits r)) <= s)%Z end).
intros b.
case b.
exists xH. exists (rexp (e + Zpos (digits m))%Z).
split.
exact (refl_equal _).
unfold good_rexp in Hge.
generalize (proj1 (proj2 (Hge _) (Zeq_le _ _ (sym_eq Hb)))).
rewrite Hb.
intro H. exact H.
exact I.
destruct (round_constant_underflow rdir _ Hge _ Hb m e) as (H1,(H2,H3)).
destruct (bracket_case_underflow m e _ Hd) as [H0|[H0|H0]].
rewrite (H1 H0).
apply H.
rewrite (H2 H0).
apply H.
rewrite (H3 H0).
apply H.
assert (forall b : bool,
  match (if b then Nsucc (Npos n) else Npos n) with
  | 0%N => True
  | Npos p => exists r : positive, exists s : Z,
    Float2 (Zpos p) (rexp (e + Zpos (digits m))%Z) = Float2 (Zpos r) s :>R
    /\ (rexp (s + Zpos (digits r)) <= s)%Z end).
intros b.
unfold Nsucc.
case b.
destruct (digits_succ n) as [H1|(_,H1)].
exists (Psucc n). exists (rexp (e + Zpos (digits m))%Z).
rewrite H1.
split.
exact (refl_equal _).
omega.
exists xH. exists (rexp (e + Zpos (digits m)) + Zpos (digits n))%Z.
split.
generalize (float2_shl_correct (Zpos xH) (rexp (e + Zpos (digits m)) + Zpos (digits n))%Z (digits n)).
simpl.
cutrewrite (rexp (e + Zpos (digits m))%Z + Zpos (digits n) - Zpos (digits n) = rexp (e + Zpos (digits m)))%Z. 2: ring.
unfold shift_pos.
rewrite <- H1.
intro H. exact H.
assert (rexp (rexp (e + Zpos (digits m)) + Zpos (digits n)) <
  rexp (e + Zpos (digits m)) + Zpos (digits n))%Z.
generalize (Zgt_pos_0 (digits n)).
omega.
exact (proj1 (Hge _) H).
exists n. exists (rexp (e + Zpos (digits m))%Z).
split.
exact (refl_equal _).
omega.
destruct (round_constant rdir rexp _ _ Hb m e) as (H1,(H2,H3)).
destruct (bracket_case _ _ _ _ Hc) as [H0|[H0|[H0|H0]]].
clear H1 H2 H3.
unfold round_pos.
rewrite <- (Zpos_pos_of_Z_minus _ _ Hd).
rewrite <- Ha.
apply H.
rewrite (H1 H0).
apply H.
rewrite (H2 H0).
apply H.
rewrite (H3 H0).
apply H.
Qed.

Lemma representable_round_extension :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall Hge : good_rexp rexp,
 forall x : R,
 exists m : Z, exists e : Z,
 round_extension rdir rexp Hge x = Float2 m e :>R /\
 rexp_representable rexp m e.
intros rdir rexp Hge x.
destruct (total_order_T 0 x) as [[Hx|Hx]|Hx].
generalize (round_extension_prop_pos rdir _ Hge _ Hx).
intros (m1,(m2,(e1,(e2,(_,(H2,_)))))).
rewrite H2.
clear H2.
unfold round.
simpl.
generalize (representable_round_pos _ (rpos_good rdir) _ Hge m1 e1).
case (round_pos (rpos rdir) rexp m1 e1) ; intros n ; case n.
intros.
exists Z0. exists Z0.
split.
exact (refl_equal _).
exact I.
intros p z (r,(s,(H1,H2))).
exists (Zpos r). exists s.
exact (conj H1 H2).
exists Z0. exists Z0.
rewrite <- Hx.
rewrite round_extension_zero.
split.
rewrite float2_zero.
exact (refl_equal _).
exact I.
generalize (round_extension_prop_neg rdir _ Hge _ Hx).
intros (m1,(m2,(e1,(e2,(_,(H2,_)))))).
rewrite H2.
clear H2.
unfold round.
simpl.
generalize (representable_round_pos _ (rneg_good rdir) _ Hge m1 e1).
case (round_pos (rneg rdir) rexp m1 e1) ; intros n ; case n.
intros.
exists Z0. exists Z0.
split.
exact (refl_equal _).
exact I.
intros p z (r,(s,(H1,H2))).
exists (Zneg r). exists s.
split. 2: exact H2.
rewrite Fopp2_correct.
rewrite H1.
rewrite <- Fopp2_correct.
apply refl_equal.
Qed.

End Gappa_round.
