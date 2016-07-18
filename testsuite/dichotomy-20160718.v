Require Import Reals Gappa_tactic.

Open Scope R_scope.

Goal forall a b,
  not (0 <= a) /\ 1 <= a -> 1 <= b <= 1.
Proof.
intros a b.
gappa.
Qed.

Goal forall a b,
  -2 <= a ->
  (not (0 <= a) -> 1 <= b <= 1) ->
  (-1 <= a -> 1 <= b <= 1) ->
  1 <= b <= 1.
Proof.
intros a b.
gappa.
Qed.

Goal forall a b,
  a <= 2 ->
  (not (0 <= a) -> 1 <= b <= 1) ->
  (-1 <= a -> 1 <= b <= 1) ->
  1 <= b <= 1.
Proof.
intros a b.
gappa.
Qed.
