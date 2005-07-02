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

Definition f32e := 149.
Definition f32p := 24.
Definition f64e := 1074.
Definition f64p := 53.
Definition f80e := 1074. (*16445.*)
Definition f80p := 64.

Definition float32ne_round := f_round (rndNE f32p f32e).
Definition rounding_float32ne := (rounding_f (rndNE f32p f32e)).
Definition float64ne_round := f_round (rndNE f64p f64e).
Definition rounding_float64ne := (rounding_f (rndNE f64p f64e)).
Definition float80ne_round := f_round (rndNE f80p f80e).
Definition rounding_float80ne := (rounding_f (rndNE f80p f80e)).

Definition float32ne_absolute_wide_helper (xi zi : FF) :=
 true.

Lemma float32ne_absolute_wide :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 float32ne_absolute_wide_helper xi zi = true ->
 IintF zi (rounding_float32ne x - x).
Admitted.

Definition float32ne_absolute_inv_helper (xi zi : FF) :=
 true.

Lemma float32ne_absolute_inv :
 forall x : R, forall xi zi : FF,
 IintF xi (rounding_float32ne x) ->
 float32ne_absolute_inv_helper xi zi = true ->
 IintF zi (rounding_float32ne x - x).
Admitted.

Definition float64ne_absolute_wide_helper (xi zi : FF) :=
 true.

Lemma float64ne_absolute_wide :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 float64ne_absolute_wide_helper xi zi = true ->
 IintF zi (rounding_float64ne x - x).
Admitted.

Definition float64ne_absolute_inv_helper (xi zi : FF) :=
 true.

Lemma float64ne_absolute_inv :
 forall x : R, forall xi zi : FF,
 IintF xi (rounding_float64ne x) ->
 float64ne_absolute_inv_helper xi zi = true ->
 IintF zi (rounding_float64ne x - x).
Admitted.

Axiom float64ne_absolute: forall A B: Prop, B -> true = true -> A.
Axiom float64ne_relative: forall A B: Prop, B -> true = true -> A.
Axiom float80ne_absolute: forall A B: Prop, B -> true = true -> A.
Axiom float80ne_relative: forall A B: Prop, B -> true = true -> A.

Axiom sterbenz :
 forall A B C D : Prop,
 forall z : R, forall zi : FF,
 A -> B -> C -> D ->
 true = true ->
 IintF zi z.

Axiom user_defined :
 forall x y : R, forall xi : FF,
 IintF xi y ->
 true = true ->
 IintF xi x.

End IA_float.
