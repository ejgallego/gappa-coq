Require Import IA_comput.
Require Import F_rnd.

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
 Fle_b (lower zi) (rnd (lower xi)) &&
 Fle_b (rnd (upper xi)) (upper zi).

Theorem f_round :
 forall rnd : rounding_operator,
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 f_round_helper (rounding_float rnd) xi zi = true ->
 IintF zi (rounding_real rnd x).
intros rnd x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
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
 IintF xi x ->
 true = true ->
 IintF zi (rounding_float_ne p e x - x).
Admitted.

Theorem float_absolute_wide_ne:
 forall p: nat, forall e: N,
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 true = true ->
 IintF zi (rounding_float_ne p e x - x).
Admitted.

Theorem float_absolute_inv_ne:
 forall p: nat, forall e: N,
 forall x : R, forall xi zi : FF,
 IintF xi (rounding_float_ne p e x) ->
 true = true ->
 IintF zi (rounding_float_ne p e x - x).
Admitted.

Axiom sterbenz :
 forall A B C D : Prop,
 forall z : R, forall zi : FF,
 A -> B -> C -> D ->
 true = true ->
 IintF zi z.

End IA_float.
