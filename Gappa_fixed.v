Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_round.

Section Gappa_fixed.

Definition fixed_shift (dst : Z) (m : N) (e : Z) :=
 dst.

Lemma fixed_shift_good :
 forall dst : Z, good_rshift (fixed_shift dst).
unfold good_rshift, fixed_shift.
intros.
apply refl_equal.
Qed.

Definition fixed_dn_ext (e : Z) :=
 round_extension rndZR rndAW (fixed_shift e) rndZR_good rndAW_good (fixed_shift_good e).

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
intros (f,(H1,H2)).
simpl.
rewrite (H2 x).
intros f.
exists ((projT1 f) x).
split.
unfold rounding_fixed_dn, fixed_dn_ext.
apply refl_equal.
simpl.

apply refl_equal.
exists (projT1 (fixed_dn_ext e1) x).
split.
apply refl_equal.
Check (fixed_dn_ext e1).

End Gappa_fixed.
