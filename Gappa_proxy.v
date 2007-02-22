Require Import Gappa_common.
Require Import Gappa_round_def.
Require Import Gappa_fixed.
Require Import Gappa_float.

Section Gappa_proxy.

Theorem fix_fixed_of_fix :
 forall rdir : round_dir, forall d xn zn : Z, forall x : R,
 FIX x xn ->
 Zle_bool zn xn = true ->
 FIX (rounding_fixed rdir d x) zn.
Admitted.

Theorem flt_fixed_of_flt :
 forall rdir : round_dir, forall d : Z,
 forall xn zn : positive, forall x : R,
 FLT x xn ->
 Zle_bool (Zpos xn) (Zpos zn) = true ->
 FLT (rounding_fixed rdir d x) zn.
Admitted.

Theorem fix_float_of_fix :
 forall rdir : round_dir, forall p : positive, forall d xn zn : Z, forall x : R,
 FIX x xn ->
 Zle_bool zn xn = true ->
 FIX (rounding_float rdir p d x) zn.
Admitted.

Theorem flt_float_of_flt :
 forall rdir : round_dir, forall p : positive, forall d : Z,
 forall xn zn : positive, forall x : R,
 FLT x xn ->
 Zle_bool (Zpos xn) (Zpos zn) = true ->
 FLT (rounding_float rdir p d x) zn.
Admitted.

Axiom relative_add : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_sub : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_mul : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_fma : forall (p : positive) (e : Z) (r1 r2 r3 : R), R.
Axiom rel_round_add : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_sub : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_mul : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_fma : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.

End Gappa_proxy.
