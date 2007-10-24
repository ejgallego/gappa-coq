Require Import Reals.
Require Import ZArith.

Section Gappa_definitions.

Record float2 : Set := Float2 {Fnum : Z; Fexp : Z}.
Coercion float2R (x : float2) := (IZR (Fnum x) * powerRZ 2 (Fexp x))%R.
Record float10 : Set := Float10 { Fnum10 : Z ; Fexp10 : Z }.
Coercion float10R := fun x : float10 => (IZR (Fnum10 x) * powerRZ 10 (Fexp10 x))%R.

Record FF: Set := makepairF { lower : float2 ; upper : float2 }.

Definition BND (x : R) (xi : FF) :=
 (lower xi <= x <= upper xi)%R.
Definition ABS (x : R) (xi : FF) :=
 (0 <= lower xi)%R /\ (lower xi <= Rabs x <= upper xi)%R.
Definition REL (x1 x2 : R) (xi : FF) :=
 exists x : R, (-1 < lower xi)%R /\ (lower xi <= x <= upper xi)%R /\ (x1 = x2 * (1 + x))%R.
Definition FIX (x : R) (n : Z) :=
 exists f : float2, float2R f = x /\ (n <= Fexp f)%Z.
Definition FLT (x : R) (n : positive) :=
 exists f : float2, float2R f = x /\ (Zabs (Fnum f) < Zpower_pos 2 n)%Z.
Definition NZR (x : R) := (x <> 0)%R.

Definition contradiction := forall P : Prop, P.

End Gappa_definitions.
