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

Definition shr (m : N) (d : positive) :=
 iter_pos d _ shr_aux (rnd_record_mk m false false).

Definition succ (rshift : N -> Z -> Z) (m : N) (e : Z) :=
 match (rshift m e) with
 | Zpos p =>
   let e' := (e - Zpos p)%Z in
   match m with
   | N0 => (Npos xH, e')
   | Npos n => (Npos (Psucc (shift_pos p n)), e')
   end
 | Z0 => (Nsucc m, e)
 | _ => (m, e)
 end.

Lemma succ_correct :
 forall rshift : N -> Z -> Z,
 forall m0 : N, forall e0 : Z,
 (rshift m0 e0 >= 0)%Z ->
 let (m1, e1) := succ rshift m0 e0 in
 (Float2 (Z_of_N m0) e0 + Float2 1 (e0 - (rshift m0 e0)) = Float2 (Z_of_N m1) e1)%R.
intros rshift m0 e0.
unfold succ.
case (rshift m0 e0).
3: intros p H ; elim H ; apply refl_equal.
intros _.
ring (e0 - 0)%Z.
unfold float2R.
simpl.
rewrite <- Rmult_plus_distr_r.
do 2 rewrite <- (Rmult_comm (powerRZ 2 e0)).
apply Rmult_eq_compat_l.
case m0.
auto with real.
simpl.
intros p.
rewrite <- S_INR.
repeat rewrite INR_IZR_INZ.
apply IZR_eq.
rewrite nat_of_P_succ_morphism.
apply refl_equal.
intros p _.
cutrewrite (Float2 (Z_of_N m0) e0 = Float2 (shl (Z_of_N m0) (Zpos p)) (e0 - Zpos p) :>R)%R.
case m0 ; unfold float2R ; simpl ; intros.
ring.
rewrite <- Rmult_plus_distr_r.
do 2 rewrite <- (Rmult_comm (powerRZ 2 (e0 - Zpos p))).
apply Rmult_eq_compat_l.
rewrite <- S_INR.
repeat rewrite INR_IZR_INZ.
apply IZR_eq.
rewrite nat_of_P_succ_morphism.
apply refl_equal.
unfold float2R.
rewrite shl_correct.
2: compute ; discriminate.
simpl.
rewrite mult_IZR.
rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Zpower_pos_nat.
replace 2%Z with (Z_of_nat 2). 2: apply refl_equal.
rewrite Zpower_nat_powerRZ.
rewrite <- powerRZ_add. 2: discrR.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
ring (Zpos p + (e0 - Zpos p))%Z.
apply refl_equal.
Qed.

Definition round (rpos rneg : rnd_record -> bool)
 (rshift : N -> Z -> Z) (f : float2) :=
 match (Fnum f) with
 | Z0 => Float2 Z0 Z0
 | Zpos p =>
   let m := Npos p in
   match rshift m (Fexp f) with
   | Zneg d =>
     let r := shr m d in
     let e := (Fexp f + Zpos d)%Z in
     let (a,b) :=
       if rpos r then succ rshift (rnd_m r) e
       else (rnd_m r, e) in
     match a with
     | N0 => Float2 Z0 Z0
     | Npos q => Float2 (Zpos q) b
     end
   | _ => f
   end
 | Zneg p =>
   let m := Npos p in
   match rshift m (Fexp f) with
   | Zneg d =>
     let r := shr m d in
     let e := (Fexp f + Zpos d)%Z in
     let (a,b) :=
       if rneg r then succ rshift (rnd_m r) e
       else (rnd_m r, e) in
     match a with
     | N0 => Float2 Z0 Z0
     | Npos q => Float2 (Zneg q) b
     end
   | _ => f
   end
 end.

Ltac caseEq f := generalize (refl_equal f) ; pattern f at -1 ; case f.

Lemma round_Z0 :
 forall rpos rneg : rnd_record -> bool,
 forall rshift : N -> Z -> Z,
 forall e : Z,
 (round rpos rneg rshift (Float2 Z0 e) = 0 :>R)%R.
intros rpos rneg rshift e.
unfold round, float2R.
simpl.
auto with real.
Qed.

Lemma round_Zneg :
 forall rpos rneg : rnd_record -> bool,
 forall rshift : N -> Z -> Z,
 forall m : positive, forall e : Z,
 round rpos rneg rshift (Float2 (Zneg m) e) = Fopp2 (round rneg rpos rshift (Fopp2 (Float2 (Zneg m) e))).
intros rpos rneg rshift m e.
unfold round, Fopp2.
simpl.
case (rshift (Npos m) e) ; intros ; simpl ; try apply refl_equal.
case (rneg (shr (Npos m) p)).
case (succ rshift (rnd_m (shr (Npos m) p)) (e + Zpos p)).
intros n q.
case n ; intros ; apply refl_equal.
case (rnd_m (shr (Npos m) p)) ; intros ; apply refl_equal.
Qed.

Definition is_even (n : N) :=
 match n with
 | N0 => true
 | Npos (xO _) => true
 | _ => false
 end.

Definition rndZR (r : rnd_record) : bool :=
 false.

Definition rndAW (r : rnd_record) : bool :=
 rnd_r r || rnd_s r.

Definition rndNE (r : rnd_record) : bool :=
 rnd_r r && (rnd_s r || negb (is_even (rnd_m r))).

Definition rndNO (r : rnd_record) : bool :=
 rnd_r r && (rnd_s r || is_even (rnd_m r)).

Definition rndNZ (r : rnd_record) : bool :=
 rnd_r r && rnd_s r.

Definition rndNA (r : rnd_record) : bool :=
 rnd_r r.

Definition rndOD (r : rnd_record) : bool :=
 (rnd_r r || rnd_s r) && is_even (rnd_m r).

Definition roundZR := round rndZR rndZR.
Definition roundAW := round rndAW rndAW.
Definition roundUP := round rndAW rndZR.
Definition roundDN := round rndZR rndAW.
Definition roundOD := round rndOD rndOD.
Definition roundNE := round rndNE rndNE.
Definition roundNO := round rndNO rndNO.
Definition roundNZ := round rndNZ rndNZ.
Definition roundNA := round rndNA rndNA.
Definition roundNU := round rndNA rndNZ.
Definition roundND := round rndNZ rndNA.

End Gappa_round.