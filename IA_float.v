Require Import IA_comput.
Require Import F_rnd.

Section IA_float.

Axiom rounding_f : (float -> float) -> R -> R.
Axiom rounding_f_correct_l :
 forall rnd : float -> float,
 forall x : R, forall y : float,
 (y <= x)%R ->
 (rnd y <= rounding_f rnd x)%R.
Axiom rounding_f_correct_r :
 forall rnd : float -> float,
 forall x : R, forall y : float,
 (x <= y)%R ->
 (rounding_f rnd x <= rnd y)%R.

Definition f_round_helper (rnd : float -> float) (xi zi : FF) :=
 Fle_b (lower zi) (rnd (lower xi)) &&
 Fle_b (rnd (upper xi)) (upper zi).

Theorem f_round :
 forall rnd : float -> float,
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 f_round_helper rnd xi zi = true ->
 IintF zi (rounding_f rnd x).
intros rnd x xi zi Hx Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fle_b_correct _ _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). clear H2. intro H2.
split ; unfold FF2RR ; simpl.
apply Rle_trans with (1 := H1).
apply rounding_f_correct_l.
apply (proj1 Hx).
apply Rle_trans with (2 := H2).
apply rounding_f_correct_r.
apply (proj2 Hx).
Qed.

Definition rounding_float_ne (p: nat) (e: N) := rounding_f (rndNE p e).
Definition float_round_ne (p: nat) (e: N) := f_round (rndNE p e).

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

Parameter add22_float64: R -> R -> R.
Axiom add22_float64_round:
 forall x y : R, forall wi zi : FF,
 IintF wi (x + y) ->
 true = true ->
 IintF zi (add22_float64 x y).
Axiom add22_float64_error:
 forall x y : R, forall wi zi : FF,
 IintF wi (Rabs (x + y)) ->
 true = true ->
 IintF zi (((add22_float64 x y) - (x + y)) / (x + y)).
Axiom add22_float64_error_inv:
 forall x y : R, forall wi zi : FF,
 IintF wi (Rabs (add22_float64 x y)) ->
 true = true ->
 IintF zi (((add22_float64 x y) - (x + y)) / (x + y)).

End IA_float.
