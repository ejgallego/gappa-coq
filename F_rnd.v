Add LoadPath "/usr/src/coq/Float".
Require Export AllFloat.

Section F_rnd.

Definition radix := 2%Z.

Definition radixMoreThanOne := TwoMoreThanOne.
Lemma radixNotZero: (0 < radix)%Z.
auto with zarith.
Qed.

Variable precision : nat.
Hypothesis precisionMoreThanOne : lt (1) precision.
Lemma precisionNotZero : ~(precision = (0)).
auto with zarith.
Qed.

Variable bExp : nat.
Definition bNum := iter_nat precision positive xO xH.
Definition bound := Bound bNum bExp.

Lemma pGivesBound : Zpos (vNum bound) = Zpower_nat radix precision.
unfold vNum, bound, bNum, Zpower_nat.
elim precision. trivial.
intros n H.
Opaque Zmult.
simpl.
rewrite <- H.
Transparent Zmult.
simpl.
apply refl_equal.
Qed.

Coercion Local float2R := FtoR radix.

Definition is_even (n : N) : bool :=
 match n with
 | N0 => true
 | Npos p =>
  match p with
  | xO _ => true
  | _ => false
  end
 end.

Fixpoint digit2 (p : positive) : nat :=
 match p with
 | xH => 1
 | xO p1 => S (digit2 p1)
 | xI p1 => S (digit2 p1)
 end.

Definition digit2_N (n : N) : nat :=
 match n with
 | N0 => 0
 | Npos p => digit2 p
 end.

Lemma digit2_N_0 :
 forall n : N,
 digit2_N n = 0 -> n = N0.
intro n.
unfold digit2_N, digit2.
destruct n.
trivial.
destruct p ; intro ; discriminate H.
Qed.

Lemma digit2_N_S :
 forall n : N, forall n0 : nat,
 digit2_N n = S n0 -> exists p, n = Npos p.
intros n n0.
unfold digit2_N.
destruct n.
intro H. discriminate H.
intro.
exists p.
trivial.
Qed.

Definition Ndiv2 (n : N) : N :=
 match n with
 | N0 => N0
 | Npos n1 =>
  match n1 with
  | xH => N0
  | xO n2 => Npos n2
  | xI n2 => Npos n2
  end
 end.

Lemma Ndiv2_mul2 :
 forall n : N,
 n = Ndouble (Ndiv2 n) \/ n = Ndouble_plus_one (Ndiv2 n).
intro n.
destruct n.
left. trivial.
destruct p ; [ right | left | right ] ; trivial.
Qed.

Record rnd_record : Set := rnd_record_mk {
  rnd_m : N ;
  rnd_e : Z ;
  rnd_g : bool ;
  rnd_s : bool
}.

Definition shr_aux (p : rnd_record) : rnd_record :=
 let s := rnd_g p || rnd_s p in
 let e := Zsucc (rnd_e p) in
 match (rnd_m p) with
 | N0 => rnd_record_mk N0 e false s
 | Npos m1 =>
  match m1 with
  | xH => rnd_record_mk N0 e true s
  | xO m2 => rnd_record_mk (Npos m2) e false s
  | xI m2 => rnd_record_mk (Npos m2) e true s
  end
 end.

Lemma shr_aux_mantissa :
 forall p : rnd_record,
 rnd_m (shr_aux p) = Ndiv2 (rnd_m p).
intro p.
unfold shr_aux, Ndiv2.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Lemma shr_aux_mantissa_digit :
 forall p : rnd_record,
 digit2_N (rnd_m (shr_aux p)) = pred (digit2_N (rnd_m p)).
intro p.
CaseEq (digit2_N (rnd_m p)) ; intros ; unfold shr_aux.
rewrite (digit2_N_0 _ H).
trivial.
generalize (digit2_N_S _ _ H).
rewrite <- H.
intro H0. elim H0. clear H H0. intros p0 H.
rewrite H.
destruct p0 ; trivial.
Qed.

Lemma shr_aux_exp :
 forall p : rnd_record,
 rnd_e (shr_aux p) = Zsucc (rnd_e p).
intro p.
unfold shr_aux.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Lemma shr_aux_guard :
 forall p : rnd_record,
 rnd_g (shr_aux p) = negb (is_even (rnd_m p)).
intro p.
unfold shr_aux, is_even.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Lemma shr_aux_sticky :
 forall p : rnd_record,
 rnd_s (shr_aux p) = rnd_g p || rnd_s p.
intro p.
unfold shr_aux.
destruct (rnd_m p) ; try destruct p0 ; trivial.
Qed.

Definition bracket (r : R) (p : rnd_record) :=
 let m := (Z_of_N (rnd_m p) * 2)%Z in
 let e := (rnd_e p - 1)%Z in
 let f0 := Float m e in
 let f1 := Float (m + 1)%Z e in
 let f2 := Float (m + 2)%Z e in
 if (rnd_g p) then
  if (rnd_s p) then (f1 < r < f2)%R else (r = f1)%R
 else
  if (rnd_s p) then (f0 < r < f1)%R else (r = f0)%R.

Lemma Rlt_Float_exp :
 forall m1 m2 : Z, forall e : Z,
 (m1 < m2)%Z -> (Float m1 e < Float m2 e)%R.
intros m1 m2 e H.
unfold float2R, FtoR.
apply Rlt_monotony_exp with (1 := radixMoreThanOne).
apply Rlt_IZR.
exact H.
Qed.

Lemma Rle_Float_exp :
 forall m1 m2 : Z, forall e : Z,
 (m1 <= m2)%Z -> (Float m1 e <= Float m2 e)%R.
intros m1 m2 e H.
unfold float2R, FtoR.
apply Rle_monotone_exp with (1 := radixMoreThanOne).
apply Rle_IZR.
exact H.
Qed.

Lemma Req_Float_exp :
 forall m1 m2 : Z, forall e : Z,
 (m1 = m2)%Z -> float2R (Float m1 e) = float2R (Float m2 e).
intros m1 m2 e H.
unfold float2R, FtoR.
simpl.
ring.
apply Rmult_eq_compat_l.
apply IZR_eq.
exact H.
Qed.

Lemma shift_float :
 forall m e : Z,
 float2R (Float m e) = float2R (Float (m * 2) (e - 1)).
intros m e.
unfold float2R, FtoR.
simpl.
rewrite mult_IZR.
replace (IZR (Zpos 2)) with 2%R.
2: trivial.
unfold Zminus.
assert (2 <> 0)%R.
auto with real.
rewrite powerRZ_add with (1 := H).
rewrite powerRZ_Zopp with (1 := H).
rewrite powerRZ_1.
field.
exact H.
Qed.

Lemma Ndiv2_even :
 forall n : N,
 is_even n = true -> (Z_of_N (Ndiv2 n) * 2)%Z = (Z_of_N n)%Z.
unfold is_even, Ndiv2.
intros n H.
destruct n ; try destruct p ; try discriminate H.
trivial.
rewrite Zmult_comm.
trivial.
Qed.

Lemma Ndiv2_odd :
 forall n : N,
 is_even n = false -> (Z_of_N (Ndiv2 n) * 2)%Z = (Z_of_N n - 1)%Z.
unfold is_even, Ndiv2.
intros n H.
destruct n ; try destruct p ; try discriminate H.
2: trivial.
rewrite Zmult_comm.
trivial.
Qed.

Lemma shr_aux_bracket :
 forall r : R, forall p : rnd_record,
 bracket r p -> bracket r (shr_aux p).
intros r p H.
unfold bracket.
rewrite (shr_aux_guard p).
rewrite (shr_aux_sticky p).
rewrite (shr_aux_mantissa p).
rewrite (shr_aux_exp p).
replace (Zsucc (rnd_e p) - 1)%Z with (rnd_e p).
2: auto with zarith.
CaseEq (is_even (rnd_m p)) ; intro H0 ;
 [ rewrite Ndiv2_even with (1 := H0) | rewrite Ndiv2_odd with (1 := H0) ] ;
 CaseEq (rnd_g p) ; intro H1 ; simpl.
unfold bracket in H. rewrite H1 in H.
clear H1.
assert (Float (Z_of_N (rnd_m p) * 2 + 1) (rnd_e p - 1) <= r < Float (Z_of_N (rnd_m p) * 2 + 2) (rnd_e p - 1))%R.
destruct (rnd_s p).
split.
apply Rlt_le with (1 := proj1 H).
exact (proj2 H).
split.
apply Req_le with (1 := (sym_eq H)).
rewrite H.
apply Rlt_Float_exp.
auto with zarith.
clear H.
split ; rewrite shift_float.
apply Rlt_le_trans with (2 := proj1 H1). clear H1.
apply Rlt_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H1). clear H1.
apply Rle_Float_exp.
auto with zarith.
CaseEq (rnd_s p) ; intro H2.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
split ; rewrite shift_float.
apply Rle_lt_trans with (2 := proj1 H). clear H.
apply Rle_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H). clear H1.
apply Rle_Float_exp.
auto with zarith.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
rewrite shift_float.
rewrite H.
apply Req_Float_exp.
apply refl_equal.
unfold bracket in H. rewrite H1 in H.
clear H1.
assert (Float (Z_of_N (rnd_m p) * 2 + 1) (rnd_e p - 1) <= r < Float (Z_of_N (rnd_m p) * 2 + 2) (rnd_e p - 1))%R.
destruct (rnd_s p).
split.
apply Rlt_le with (1 := proj1 H).
exact (proj2 H).
split.
apply Req_le with (1 := (sym_eq H)).
rewrite H.
apply Rlt_Float_exp.
auto with zarith.
clear H.
split ; rewrite shift_float.
apply Rlt_le_trans with (2 := proj1 H1). clear H1.
apply Rlt_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H1). clear H1.
apply Rle_Float_exp.
auto with zarith.
CaseEq (rnd_s p) ; intro H2.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
split ; rewrite shift_float.
apply Rle_lt_trans with (2 := proj1 H). clear H.
apply Rle_Float_exp.
auto with zarith.
apply Rlt_le_trans with (1 := proj2 H). clear H1.
apply Rle_Float_exp.
auto with zarith.
unfold bracket in H. rewrite H1 in H. rewrite H2 in H.
rewrite shift_float.
rewrite H.
apply Req_Float_exp.
ring.
Qed.

Fixpoint shr (p : rnd_record) (n : nat) { struct n } : rnd_record :=
 match n with
 | O => p
 | S n1 => shr (shr_aux p) n1
 end.

Lemma shr_mantissa_digit :
 forall n : nat, forall p : rnd_record,
 digit2_N (rnd_m (shr p n)) = digit2_N (rnd_m p) - n.
induction n ; intro p.
apply minus_n_O.
unfold shr. fold shr.
replace (digit2_N (rnd_m p) - S n) with
 (pred (digit2_N (rnd_m p)) - n).
rewrite <- shr_aux_mantissa_digit.
apply IHn.
destruct (digit2_N (rnd_m p)) ; trivial.
Qed.

Lemma shr_exp :
 forall n : nat, forall p : rnd_record,
 rnd_e (shr p n) = (rnd_e p + n)%Z.
induction n ; intro p.
auto with zarith.
unfold shr. fold shr.
rewrite IHn.
rewrite shr_aux_exp.
rewrite inj_S.
auto with zarith.
Qed.

Lemma shr_bracket :
 forall r : R, forall n : nat, forall p : rnd_record,
 bracket r p -> bracket r (shr p n).
induction n ; intro p.
trivial.
unfold shr. fold shr.
intro H.
apply IHn.
apply shr_aux_bracket with (1 := H).
Qed.

Fixpoint shl_aux (p : positive) (n : nat) { struct n } : positive :=
 match n with
 | O => p
 | S p1 => shl_aux (xO p) p1
 end.

Definition shl (m : positive) (e : Z) (n : nat) : rnd_record :=
 rnd_record_mk (Npos (shl_aux m n)) (e - n) false false.

Lemma shl_mantissa_digit :
 forall m : positive, forall e : Z, forall n : nat,
 digit2_N (rnd_m (shl m e n)) = digit2 m + n.
assert (forall n : nat, forall p : positive, digit2 (shl_aux p n) = digit2 p + n).
induction n.
trivial.
intro p.
simpl.
rewrite IHn.
simpl.
apply plus_n_Sm.
intros.
simpl.
apply H.
Qed.

Definition rnd_aux (m : positive) (e : Z) : rnd_record :=
 let n := digit2 m in
 if le_lt_dec n precision then
  shl m e (precision - n)
 else
  shr (rnd_record_mk (Npos m) e false false) (n - precision).

Lemma rnd_aux_mantissa_digit :
 forall m : positive, forall e : Z,
 digit2_N (rnd_m (rnd_aux m e)) = precision.
intros m e.
unfold rnd_aux.
destruct (le_lt_dec (digit2 m) precision).
rewrite shl_mantissa_digit.
auto with arith.
rewrite shr_mantissa_digit.
simpl.
apply sym_eq.
apply plus_minus.
rewrite plus_comm.
info auto with arith.
Qed.

Lemma digit2_size :
 forall m : positive,
 let n := digit2 m in
 (Zpower_nat 2 n <= 2 * Zpos m)%Z /\ (Zpos m < Zpower_nat 2 n)%Z.
induction m.
simpl.
Admitted.

Lemma fast_canonic :
 forall f : float,
 Fbounded bound f ->
 (Fexp f = -bExp)%Z \/ (Zpos (vNum bound) <= Zabs (radix * Fnum f))%Z ->
 Fcanonic radix bound f.
intros f B H.
destruct H.
destruct (Z_lt_le_dec (Zabs (radix * Fnum f))%Z (Zpos bNum)).
right. repeat ( split ; trivial ).
left. repeat ( split ; trivial ).
left. repeat ( split ; trivial ).
Qed.

Axiom plouf : forall P, P.

Definition rnd (m : positive) (e : Z) : rnd_record :=
 let r := rnd_aux m e in
 if Zle_bool (rnd_e r) (-bExp) then
  shr r (Zabs_nat (bExp + (rnd_e r)))
 else r.

Lemma rnd_canonic :
 forall m : positive, forall e : Z,
 let r := rnd m e in
 Fcanonic radix bound (Float (Z_of_N (rnd_m r)) (rnd_e r)).
intros m e.
unfold rnd.
generalize (Zle_cases (rnd_e (rnd_aux m e)) (-bExp)%Z).
destruct (Zle_bool (rnd_e (rnd_aux m e)) (-bExp)%Z) ; intro H.
apply fast_canonic.
apply plouf.
left.
simpl.
rewrite shr_exp.
assert (forall n : Z, Z_of_nat (Zabs_nat n) = Zabs n).
destruct n ; simpl ; try rewrite Zpos_eq_Z_of_nat_o_nat_of_P ; trivial.
rewrite H0. clear H0.
rewrite Zabs_non_eq.
ring.
auto with zarith.
assert (forall n : N, Zabs (Z_of_N n) = Z_of_N n).
destruct n ; trivial.
apply fast_canonic.
generalize (Zgt_lt _ _ H). clear H. intro H.
unfold Fbounded.
split.
2: auto with zarith.
rewrite pGivesBound.
rewrite <- (rnd_aux_mantissa_digit m e).
simpl.
rewrite H0. clear H0.
destruct (rnd_m (rnd_aux m e)).
unfold Zpower_nat.
auto with zarith.
unfold Z_of_N, digit2_N.
apply (proj2 (digit2_size p)).
right.
rewrite Zabs_Zmult.
rewrite pGivesBound.
simpl.
rewrite H0. clear H0.
generalize precisionNotZero.
rewrite <- (rnd_aux_mantissa_digit m e).
destruct (rnd_m (rnd_aux m e)) ; intro H0.
elim H0. trivial.
clear H0. simpl.
apply (proj1 (digit2_size p)).
Qed.

Axiom rnd_bracket :
 forall m : positive, forall e : Z,
 bracket (Float (Zpos m) e) (rnd m e).

Axiom rnd_exp_zero :
 forall m : positive, forall e : Z,
 let r := rnd m e in
 rnd_m r = N0 -> (rnd_e r = -bExp)%Z.

Definition rndZ_fun (r : rnd_record) : bool := false.

Definition rndU_fun (r : rnd_record) : bool :=
 rnd_g r || rnd_s r.

Definition rndO_fun (r : rnd_record) : bool :=
 (rnd_g r || rnd_s r) && is_even (rnd_m r).

Definition rndCE_fun (r : rnd_record) : bool :=
 rnd_g r && (rnd_s r || negb (is_even (rnd_m r))).

Definition rndCU_fun (r : rnd_record) : bool :=
 rnd_g r.

Definition do_rnd (m : positive) (e : Z) (g : rnd_record -> bool) : float :=
 let r := rnd_aux m e in
 let f := Float (Z_of_N (rnd_m r)) (rnd_e r) in
 if (g r) then FSucc bound radix precision f else f.

Definition do_rnd2 (gp gn : rnd_record -> bool) (f : float) : float :=
 match (Fnum f) with
 | Z0 => Float 0 (-bExp)
 | Zpos p =>
  do_rnd p (Fexp f) gp
 | Zneg p =>
  Fopp (do_rnd p (Fexp f) gn)
 end.

Definition rndZ := do_rnd2 rndZ_fun rndZ_fun.
Definition rndU := do_rnd2 rndU_fun rndZ_fun.
Definition rndD := do_rnd2 rndZ_fun rndU_fun.
Definition rndO := do_rnd2 rndO_fun rndO_fun.
Definition rndCE := do_rnd2 rndCE_fun rndCE_fun.
Definition rndCU := do_rnd2 rndCU_fun rndCU_fun.

End F_rnd.
