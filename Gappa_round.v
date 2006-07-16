Require Import Classical.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_dyadic.

Section Gappa_round.

Record rnd_record : Set := rnd_record_mk {
  rnd_m : N ;
  rnd_r : bool ;
  rnd_s : bool
}.

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

Lemma float2_shift1 :
 forall m : Z, forall e : Z,
 Float2 m (e + 1) = Float2 (m * 2) e :>R.
intros m e.
unfold float2R. simpl.
rewrite powerRZ_add. 2: discrR.
simpl.
rewrite mult_IZR.
replace (IZR 2) with 2%R. 2: apply refl_equal.
ring.
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

Definition bracket (r : R) (p : rnd_record) (e : Z) :=
 let m := (Z_of_N (rnd_m p) * 2)%Z in
 let f0 := Float2 m e in
 let f1 := Float2 (m + 1)%Z e in
 let f2 := Float2 (m + 2)%Z e in
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
              (Float2 (Z_of_N (rnd_m p) * 2) e < r < Float2 ((Z_of_N (rnd_m p) + 1) * 2) e)%R
            else r = Float2 (Z_of_N (rnd_m p) * 2) e).
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
rewrite H1. clear H0 H1.
repeat rewrite (float2_shift1).
exact HH.
assert (Z_of_N (rnd_m (shr_aux p)) * 2 = Z_of_N (rnd_m p))%Z.
generalize H0. unfold shr_aux.
destruct (rnd_m p).
intros _. apply refl_equal.
destruct p0.
intros H1. discriminate H1.
intros _. simpl. rewrite Pmult_comm. apply refl_equal.
intros H1. discriminate H1.
rewrite H1. clear H0 H1.
repeat rewrite (float2_shift1).
exact HH.
Qed.

Definition shr (m : N) (d : positive) :=
 iter_pos d _ shr_aux (rnd_record_mk m false false).

Lemma shr_bracket :
 forall r : R, forall d : positive,
 forall m : N, forall e : Z,
 bracket r (rnd_record_mk m false false) e ->
 bracket r (shr m d) (e + Zpos d).
intros r d m e H.
unfold shr.
assert (let (rnd', e') :=
          iter_pos d _
            (fun u => match u with (rnd, e) => (shr_aux rnd, (e + 1)%Z) end)
            (rnd_record_mk m false false, e) in
        bracket r rnd' e').
apply iter_pos_invariant.
intros (rnd',e').
apply shr_aux_bracket.
exact H.
assert (iter_pos d _
          (fun u => match u with (rnd, e) => (shr_aux rnd, (e + 1)%Z) end)
          (rnd_record_mk m false false, e)
        = (iter_pos d _ shr_aux (rnd_record_mk m false false),
           iter_pos d _ (fun e => (e + 1)%Z) e)).
intros.
repeat rewrite (iter_nat_of_P d).
induction (nat_of_P d).
apply refl_equal.
simpl.
rewrite IHn.
apply refl_equal.
rewrite H1 in H0.
cut (forall a b, a + Zpos b = iter_pos b Z (fun c : Z => (c + 1)%Z) a)%Z.
intros.
rewrite (H2 e d).
exact H0.
clear H H0 H1 r m.
Admitted.

Fixpoint digits (m : positive) : positive :=
 match m with
 | xH => xH
 | xI p => Psucc (digits p)
 | xO p => Psucc (digits p)
 end.

Lemma digits_correct :
 forall m : positive,
 (powerRZ 2 (Zpos (digits m) - 1)%Z <= IZR (Zpos m) < powerRZ 2 (Zpos (digits m)))%R.
induction m.
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

Definition round_pos (rdir : rnd_record -> bool)
  (rexp : Z -> Z) (m : positive) (e : Z) :=
 let e' := rexp (e + Zpos (digits m))%Z in
 match (e' - e)%Z with
 | Zpos d =>
   let r := shr (Npos m) d in
   ((if rdir r then Nsucc (rnd_m r) else rnd_m r), e')
 | _ => (Npos m, e)
 end.

(*
Lemma round_Z0 :
 forall rpos rneg : rnd_record -> bool,
 forall rexp : Z -> Z,
 forall e : Z,
 (round rpos rneg rexp (Float2 Z0 e) = 0 :>R)%R.
intros rpos rneg rexp e.
unfold round, float2R.
simpl.
auto with real.
Qed.

Lemma round_Zneg :
 forall rpos rneg : rnd_record -> bool,
 forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 round rpos rneg rexp (Float2 (Zneg m) e) = Fopp2 (round rneg rpos rexp (Fopp2 (Float2 (Zneg m) e))).
intros rpos rneg rexp m e.
unfold round, Fopp2.
simpl.
case (rexp (e + Zpos (digits m)) - e)%Z ; intros ; simpl ; try apply refl_equal.
case (rneg (shr (Npos m) p)).
case (Nsucc (rnd_m (shr (Npos m) p))).
apply refl_equal.
intros q.
apply refl_equal.
case (rnd_m (shr (Npos m) p)) ; intros ; apply refl_equal.
Qed.

Lemma round_rexp_exact :
 forall rpos rneg : rnd_record -> bool,
 forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 (rexp (e + Zpos (digits m)) <= e)%Z ->
 (round rpos rneg rexp (Float2 (Zpos m) e) = Float2 (Zpos m) e :>R)%R.
intros rpos rneg rexp m e H.
unfold round.
simpl.
caseEq (rexp (e + Zpos (digits m)) - e)%Z ; intros ; try apply refl_equal.
elim H.
rewrite <- (Zcompare_plus_compat (rexp (e + Zpos (digits m))%Z) e (-e)).
rewrite Zplus_opp_l.
rewrite Zplus_comm.
unfold Zminus in H0.
rewrite H0.
apply refl_equal.
Qed.

Lemma repartition :
 forall m1 m2 : positive, forall e1 e2 : Z,
 (Float2 (Zpos m1) e1 <= Float2 (Zpos m2) e2 < Float2 (Zpos (Psucc m1)) e1)%R ->
 (e1 + Zpos (digits m1) = e2 + Zpos (digits m2))%Z.
intros m1 m2 e1 e2 (H1,H2).

Lemma round_constant :
 forall rpos rneg : rnd_record -> bool,
 forall rexp : Z -> Z,
 forall m : positive, forall e : Z,
 (rexp (e + Zpos (digits m)) = e)%Z ->
 forall f : float2,
 ((Float2 (Zpos m) e < f < Float2 (Zpos (xI m)) (e - 1))%R
   -> round rpos rneg rexp f = round rpos rneg rexp (Float2 (Zpos (xI (xO m))) (e - 2))) /\
 ((Float2 (Zpos (xI m)) (e - 1) < f < Float2 (Zpos (Psucc m)) e)%R
   -> round rpos rneg rexp f = round rpos rneg rexp (Float2 (Zpos (xI (xI m))) (e - 2))).
intros rpos rneg rexp m e H f.
split ; intro H0.
unfold round. simpl.
*)

Definition is_even (n : N) :=
 match n with
 | N0 => true
 | Npos (xO _) => true
 | _ => false
 end.

Definition good_rdir (rdir: rnd_record -> bool) :=
 forall m : N,
 rdir (rnd_record_mk m false false) = false /\
 (rdir (rnd_record_mk m false true) = false \/ rdir (rnd_record_mk m true false) = true) /\
 (rdir (rnd_record_mk m true false) = false \/ rdir (rnd_record_mk m true true) = true).

Record round_dir : Set := round_dir_mk {
 rpos : rnd_record -> bool ;
 rneg : rnd_record -> bool ;
 rpos_good : good_rdir rpos ;
 rneg_good : good_rdir rneg
}.

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

Definition rndZR (r : rnd_record) : bool :=
 false.

Lemma rndZR_good : good_rdir rndZR.
unfold good_rdir, rndZR. simpl.
intuition.
Qed.

Definition rndAW (r : rnd_record) : bool :=
 rnd_r r || rnd_s r.

Lemma rndAW_good : good_rdir rndAW.
unfold good_rdir, rndAW. simpl.
intuition.
Qed.

Definition rndNE (r : rnd_record) : bool :=
 rnd_r r && (rnd_s r || negb (is_even (rnd_m r))).

Lemma rndNE_good : good_rdir rndNE.
unfold good_rdir, rndNE. simpl.
intuition.
Qed.

Definition rndNO (r : rnd_record) : bool :=
 rnd_r r && (rnd_s r || is_even (rnd_m r)).

Lemma rndNO_good : good_rdir rndNO.
unfold good_rdir, rndNO. simpl.
intuition.
Qed.

Definition rndNZ (r : rnd_record) : bool :=
 rnd_r r && rnd_s r.

Lemma rndNZ_good : good_rdir rndNZ.
unfold good_rdir, rndNZ. simpl.
intuition.
Qed.

Definition rndNA (r : rnd_record) : bool :=
 rnd_r r.

Lemma rndNA_good : good_rdir rndNA.
unfold good_rdir, rndNA. simpl.
intuition.
Qed.

Definition rndOD (r : rnd_record) : bool :=
 (rnd_r r || rnd_s r) && is_even (rnd_m r).

Lemma rndOD_good : good_rdir rndOD.
unfold good_rdir, rndOD. simpl.
intros.
case (is_even m) ; intuition.
Qed.

Definition roundZR := round_dir_mk rndZR rndZR rndZR_good rndZR_good.
Definition roundAW := round_dir_mk rndAW rndAW rndAW_good rndAW_good.
Definition roundUP := round_dir_mk rndAW rndZR rndAW_good rndZR_good.
Definition roundDN := round_dir_mk rndZR rndAW rndZR_good rndAW_good.
Definition roundOD := round_dir_mk rndOD rndOD rndOD_good rndOD_good.
Definition roundNE := round_dir_mk rndNE rndNE rndNE_good rndNE_good.
Definition roundNO := round_dir_mk rndNO rndNO rndNO_good rndNO_good.
Definition roundNZ := round_dir_mk rndNZ rndNZ rndNZ_good rndNZ_good.
Definition roundNA := round_dir_mk rndNA rndNA rndNA_good rndNA_good.
Definition roundNU := round_dir_mk rndNA rndNZ rndNA_good rndNZ_good.
Definition roundND := round_dir_mk rndNZ rndNA rndNZ_good rndNA_good.

Axiom round_extension :
 forall rdir : round_dir, forall rexp : Z -> Z,
 sigT (fun fext : R -> float2 =>
 (forall x y : R, (fext x <= fext y)%R) /\
 (forall f : float2, fext f = round rdir rexp f)).

Lemma round_neighbor :
 forall rdir : round_dir, forall rexp : Z -> Z,
 forall fext : R -> float2,
 (forall x y : R, (fext x <= fext y)%R) /\
 (forall f : float2, fext f = round rdir rexp f) ->
 forall r : R,
 exists x : float2, exists y : float2,
 (x <= r <= y)%R /\
 round rdir rexp x = round rdir rexp y.
intros rdir rexp fext (Hext1,Hext2) r.
generalize (classic (exists z : float2, r = z)).
intros [(z,H)|H].
exists z.
exists z.
split.
auto with real.
apply refl_equal.
Admitted.

End Gappa_round.
