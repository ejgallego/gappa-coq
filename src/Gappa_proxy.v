Require Import Gappa_common.
Require Import Gappa_round_def.
Require Import Gappa_fixed.
Require Import Gappa_float.

Section Gappa_proxy.

Axiom bnd_div_of_rel_bnd_div :
 forall x1 x2 y : R, forall xi yi zi : FF,
 REL x1 x2 xi -> BND (x2 / y) yi ->
 true = true ->
 BND ((x1 - x2) / y) zi.

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
