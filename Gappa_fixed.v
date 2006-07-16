Require Import Classical.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_round.

Section Gappa_fixed.

Definition fixed_shift (e : Z) (_ : Z) := e.

Definition fixed_dn_ext (e : Z) :=
 round_extension roundDN (fixed_shift e).

Definition rounding_fixed_dn (e : Z) (x : R) :=
 float2R (projT1 (fixed_dn_ext e) x).

Theorem fix_of_fixed_dn :
 forall x : R, forall e1 e2 : Z,
 Zle_bool e2 e1 = true ->
 FIX (rounding_fixed_dn e1 x) e2.
intros x e1 e2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX.
exists (projT1 (fixed_dn_ext e1) x).
split.
apply refl_equal.
generalize (fixed_dn_ext e1).
intros (f,H1).
simpl.
generalize (round_neighbor roundDN (fixed_shift e1) f H1 x).
intros (a,(b,(H2,H3))).
generalize (proj1 H1 a x). intro H4.
generalize (proj1 H1 x b). intro H5.
rewrite <- (proj2 H1 a) in H3.
rewrite <- (proj2 H1 b) in H3.
rewrite <- H3 in H5.
rewrite <- (Rle_antisym (f a) (f x) H4 H5).

End Gappa_fixed.
