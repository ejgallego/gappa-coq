Require Import IA_comput.

Section IA_float.

Axiom rounding_float32ne : R -> R.

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

Definition float32ne_round_helper (xi zi : FF) :=
 true.

Lemma float32ne_round :
 forall x : R, forall xi zi : FF,
 IintF xi x ->
 float32ne_round_helper xi zi = true ->
 IintF zi (rounding_float32ne x).
Admitted.

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

(*
Definition union_helper (xi1 xi2 zi zi1 zi2 : FF) :=
 true.

Axiom union :
 forall x z : R, forall xi1 xi2 zi zi1 zi2 : FF,
 (IintF xi1 x -> IintF zi1 z) ->
 (IintF xi2 x -> IintF zi2 z) ->
 union_helper xi1 xi2 zi zi1 zi2 = true ->
 IintF (makepairF (lower xi1) (upper xi2)) x ->
 IintF zi z.

Lemma l1 : p1 -> p2.
 intros h0.
 unfold p2.
 assert (u0 : p3 -> p2).
 intros u0h. apply l2. exact u0h.
 assert (u1 : p7 -> p8).
 intros u1h. apply l9. exact u1h.
 unfold p2, p3, p7, p8 in u0, u1.
 apply union with (1 := u0) (2 := u1).
 reflexivity.
 exact h0.
Qed.
*)

End IA_float.
