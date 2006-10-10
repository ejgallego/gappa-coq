Require Import Gappa_common.
Require Import Gappa_round_def.
Require Import Gappa_round_aux.
Require Import Gappa_round.
Require Import Gappa_float.

Section Gappa_proxy.

Definition float_ulp (p : positive) (d m e : Z) :=
 match m with
 | Zpos n => float_shift p d (e + Zpos (digits n))%Z
 | Zneg n => float_shift p d (e + Zpos (digits n))%Z
 | Z0 => (-d)%Z
 end.

Definition float_absolute_ne_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 1)%Z in
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS x xi ->
 float_absolute_ne_helper p d xi zi = true ->
 BND (rounding_float roundNE p d x - x) zi.
Admitted.

Definition float_absolute_wide_ne_helper (p : positive) (d : Z) (xi : FF) (zi : FF) :=
 let u := upper xi in
 let e := (float_ulp p d (Fnum u) (Fexp u) - 2)%Z in
 Fle2 u (Float2 (Zpos (xI (shift_pos p xH))) e) &&
 Fle2 (lower zi) (Float2 (-1) e) &&
 Fle2 (Float2 1 e) (upper zi).

Theorem float_absolute_wide_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS x xi ->
 float_absolute_wide_ne_helper p d xi zi = true ->
 BND (rounding_float roundNE p d x - x) zi.
Admitted.

End Gappa_proxy.
