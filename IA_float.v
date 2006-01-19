Require Import F_rnd.
Require Import Gappa_common.

Section IA_float.

Record rounding_operator : Set := mk_rounding {
 rounding_real : R -> R;
 rounding_float : float -> float;
 rounding_coerc : forall f : float,
  rounding_real f = float2R (rounding_float f);
 rounding_mono : forall x y : R,
  (x <= y)%R -> (rounding_real x <= rounding_real y)%R
}.

Definition f_round_helper (rnd : float -> float) (xi zi : FF) :=
 Fle2 (lower zi) (rnd (lower xi)) &&
 Fle2 (rnd (upper xi)) (upper zi).

Theorem f_round :
 forall rnd : rounding_operator,
 forall x : R, forall xi zi : FF,
 BND x xi ->
 f_round_helper (rounding_float rnd) xi zi = true ->
 BND (rounding_real rnd x) zi.
intros rnd x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle2_correct _ _ H1). clear H1. intro H1.
generalize (Fle2_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1).
rewrite <- (rounding_coerc rnd (lower xi)).
apply rounding_mono with (1 := proj1 Hx).
apply Rle_trans with (2 := H2).
rewrite <- (rounding_coerc rnd (upper xi)).
apply rounding_mono with (1 := proj2 Hx).
Qed.

Parameter dummy_rounding_ne_real : nat -> N -> R -> R.
Parameter dummy_rounding_ne_coerc :
 forall p : nat, forall e : N, forall f : float,
 dummy_rounding_ne_real p e f = float2R (rndNE p e f).
Parameter dummy_rounding_ne_mono :
 forall p : nat, forall e : N, forall x y : R,
 (x <= y)%R ->
 (dummy_rounding_ne_real p e x <= dummy_rounding_ne_real p e y)%R.
Definition rounding_ne (p : nat) (e : N) :=
 mk_rounding (dummy_rounding_ne_real p e) (rndNE p e)
  (dummy_rounding_ne_coerc p e) (dummy_rounding_ne_mono p e).

Definition rounding_float_ne (p: nat) (e: N) :=
 rounding_real (rounding_ne p e).
Definition float_round_ne (p: nat) (e: N) :=
 f_round (rounding_ne p e).

Theorem float_absolute_ne:
 forall p: nat, forall e: N,
 forall x : R, forall xi zi : FF,
 BND x xi ->
 true = true ->
 BND (rounding_float_ne p e x - x) zi.
Admitted.

Theorem float_absolute_wide_ne:
 forall p: nat, forall e: N,
 forall x : R, forall xi zi : FF,
 BND x xi ->
 true = true ->
 BND (rounding_float_ne p e x - x) zi.
Admitted.

Theorem float_absolute_inv_ne:
 forall p: nat, forall e: N,
 forall x : R, forall xi zi : FF,
 BND (rounding_float_ne p e x) xi ->
 true = true ->
 BND (rounding_float_ne p e x - x) zi.
Admitted.

Parameter rounding_fixed_zr : Z -> R -> R.
Parameter rounding_fixed_ne : Z -> R -> R.

Axiom rounding_fixed_ne_correct_1 :
 forall n : Z, forall x : R,
 FIX (rounding_fixed_ne n x) n.
Axiom rounding_fixed_ne_correct_2 :
 forall n e : Z, forall x : R,
 FIX x n -> (n <= e)%Z ->
 exists f : float, x = rounding_fixed_ne n f.
Axiom fix_of_fixed :
 forall n e : Z, forall x : R,
 (Zle_bool n e) = true -> FIX (rounding_fixed_ne e x) n.
Axiom flt_of_float :
 forall n : positive, forall p : nat, forall e : N, forall x : R,
 (Zle_bool (Z_of_nat p) (Zpos n)) = true -> FLT (rounding_float_ne p e x) n.
Definition contains_zero_helper (zi : FF) :=
 Fneg0 (lower zi) &&
 Fpos0 (upper zi).
Axiom fixed_of_fix :
 forall n e : Z, forall zi : FF, forall x : R,
 FIX x n ->
 Zle_bool e n && contains_zero_helper zi = true ->
 BND (rounding_fixed_ne e x - x) zi.
Axiom float_of_fix_flt :
 forall n : Z, forall e : N, forall zi : FF, forall x : R, forall m : positive, forall p : nat,
 FIX x n -> FLT x m ->
 Zle_bool (Zopp (Z_of_N e)) n && Zle_bool (Zpos m) (Z_of_nat p) && contains_zero_helper zi = true ->
 BND (rounding_float_ne p e x - x) zi.

End IA_float.
