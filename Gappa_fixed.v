Require Import Classical.
Require Import ZArith.
Require Import Reals.
Require Import Gappa_definitions.
Require Import Gappa_round.

Section Gappa_fixed.

Definition fixed_shift (e : Z) (_ : Z) := e.

Definition fixed_ext (rdir : round_dir) (e : Z) :=
 round_extension rdir (fixed_shift e).

Definition rounding_fixed (rdir : round_dir) (e : Z) :=
 projT1 (fixed_ext rdir e).

Axiom log2:
 forall x : R, (0 < x)%R ->
 exists k : Z, (powerRZ 2 (k - 1) <= x < powerRZ 2 k)%R.

Theorem fix_of_fixed :
 forall rdir : round_dir,
 forall x : R, forall e1 e2 : Z,
 Zle_bool e2 e1 = true ->
 FIX (rounding_fixed rdir e1 x) e2.
intros rdir x e1 e2 H.
generalize (Zle_bool_imp_le _ _ H). clear H. intro H.
unfold FIX.
unfold rounding_fixed.
generalize (fixed_ext rdir e1).
intros (fext,(H1,(H2,H3))).
simpl.
case (Req_dec (fext x) R0) ; intro H0.
exists (Float2 Z0 e1).
split. 2: exact H.
rewrite H0.
unfold float2R.
apply Rmult_0_l.
case (Req_dec x R0).
intro H4.
elim H0.
replace x with (float2R (Float2 Z0 e1)).
rewrite (H2 (Float2 Z0 e1)).
unfold round.
simpl.
unfold float2R.
apply Rmult_0_l.
rewrite H4.
unfold float2R.
apply Rmult_0_l.
intros H4.
assert (0 < Rabs x)%R.
apply Rabs_pos_lt with (1 := H4).
generalize (log2 (Rabs x) H5).
intros (k,H6).
generalize (H3 x k H6).
intros (f,(H7,H8)).
exists f.
split.
apply sym_eq with (1 := H7).
rewrite H8.
exact H.
Qed.

End Gappa_fixed.
