Require Import Gappa_common.

Section Gappa_proxy.

Axiom relative_add : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_sub : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_mul : forall (p : positive) (e : Z) (r1 r2 : R), R.
Axiom relative_fma : forall (p : positive) (e : Z) (r1 r2 r3 : R), R.
Axiom rel_round_add : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_sub : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_mul : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.
Axiom rel_round_fma : forall (p : positive) (e : Z) (Q P : Prop), Q -> P.

End Gappa_proxy.
