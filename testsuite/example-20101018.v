From Coq Require Import Reals.
From Flocq Require Import Core.
From Gappa Require Import Gappa_tactic.
Open Scope R_scope.

Definition format :=
  generic_format radix2 (FLT_exp (-1074) 53).

Goal
  forall a b : R,
  format a -> format b ->
  52 / 16 <= a <= 53 / 16 ->
  22 / 16 <= b <= 30 / 16 ->
  format (a - b).
Proof.
  unfold format ; gappa.
Qed.
