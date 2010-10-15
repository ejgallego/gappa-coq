Require Import Gappa_common.
Require Import Gappa_round_def.
Require Import Gappa_fixed.
Require Import Gappa_float.

Section Gappa_proxy.

Theorem fix_fixed_of_fix :
 forall rdir d xn zn x,
 FIX x xn ->
 Zle_bool zn xn = true ->
 FIX (rounding_fixed rdir d x) zn.
Admitted.

Theorem flt_fixed_of_flt :
 forall rdir d xn zn x,
 FLT x xn ->
 Zle_bool (Zpos xn) (Zpos zn) = true ->
 FLT (rounding_fixed rdir d x) zn.
Admitted.

Theorem fix_float_of_fix :
 forall rdir p d xn zn x,
 FIX x xn ->
 Zle_bool zn xn = true ->
 FIX (rounding_float rdir p d x) zn.
Admitted.

Theorem flt_float_of_flt :
 forall rdir p d xn zn x,
 FLT x xn ->
 Zle_bool (Zpos xn) (Zpos zn) = true ->
 FLT (rounding_float rdir p d x) zn.
Admitted.

Axiom add_rr :
 forall x1 x2 y1 y2 : R, forall xi yi qi zi : FF,
 REL x1 x2 xi -> REL y1 y2 yi -> BND (x2 / (x2 + y2)) qi -> NZR (x2 + y2) ->
 true = true ->
 REL (x1 + y1) (x2 + y2) zi.

Axiom sub_rr :
 forall x1 x2 y1 y2 : R, forall xi yi qi zi : FF,
 REL x1 x2 xi -> REL y1 y2 yi -> BND (x2 / (x2 - y2)) qi -> NZR (x2 - y2) ->
 true = true ->
 REL (x1 - y1) (x2 - y2) zi.

Axiom bnd_div_of_rel_bnd_div :
 forall x1 x2 y : R, forall xi yi zi : FF,
 REL x1 x2 xi -> BND (x2 / y) yi ->
 true = true ->
 BND ((x1 - x2) / y) zi.

Axiom float_absolute_inv_ne :
 forall p : positive, forall d : Z, forall x : R, forall xi zi : FF,
 ABS (rounding_float Fcore_rnd_ne.rndNE p d x) xi ->
 float_absolute_n_helper p d xi zi = true ->
 BND (rounding_float Fcore_rnd_ne.rndNE p d x - x) zi.

Axiom relative_add : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_sub : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_mul : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_fma : forall (p : positive) (e : Z) (r1 r2 r3 : R), R.
Axiom rel_round_add : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_sub : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_mul : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_fma : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_error_add : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_error_sub : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_error_mul : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_error_fma : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.

End Gappa_proxy.
