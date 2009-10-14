Require Import Gappa_common.
Require Import Gappa_pred_bnd.

Section Gappa_user.

Definition rewrite_ne_helper (xi : FF) (n : Z) :=
 Flt2 (upper xi) (Float2 n 0) || Flt2 (Float2 n 0) (lower xi).

Lemma rewrite_ne :
 forall x : R, forall xi : FF, forall n : Z, BND x xi ->
 rewrite_ne_helper xi n = true ->
 (x <> Float1 n)%R.
intros x xi n Hx Hb.
destruct (orb_prop _ _ Hb) as [H|H] ; clear Hb.
generalize (Flt2_correct _ _ H). clear H. intro H.
apply Rlt_not_eq.
apply Rle_lt_trans with (1 := proj2 Hx).
exact H.
generalize (Flt2_correct _ _ H). clear H. intro H.
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (2 := proj1 Hx).
exact H.
Qed.

Definition rewrite_lt_helper (xi : FF) (n : Z) :=
 Flt2 (upper xi) (Float2 n 0).

Lemma rewrite_lt :
 forall x : R, forall xi : FF, forall n : Z, BND x xi ->
 rewrite_lt_helper xi n = true ->
 (x < Float1 n)%R.
intros x xi n Hx Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
apply Rle_lt_trans with (1 := proj2 Hx).
exact H.
Qed.

Definition rewrite_le_helper (xi : FF) (n : Z) :=
 Fle2 (upper xi) (Float2 n 0).

Lemma rewrite_le :
 forall x : R, forall xi : FF, forall n : Z, BND x xi ->
 rewrite_le_helper xi n = true ->
 (x <= Float1 n)%R.
intros x xi n Hx Hb.
generalize (Fle2_correct _ _ Hb). clear Hb. intro H.
apply Rle_trans with (1 := proj2 Hx).
exact H.
Qed.

Definition rewrite_gt_helper (xi : FF) (n : Z) :=
 Flt2 (Float2 n 0) (lower xi).

Lemma rewrite_gt :
 forall x : R, forall xi : FF, forall n : Z, BND x xi ->
 rewrite_gt_helper xi n = true ->
 (x > Float1 n)%R.
intros x xi n Hx Hb.
generalize (Flt2_correct _ _ Hb). clear Hb. intro H.
unfold Rgt.
apply Rlt_le_trans with (2 := proj1 Hx).
exact H.
Qed.

Definition rewrite_ge_helper (xi : FF) (n : Z) :=
 Fle2 (Float2 n 0) (lower xi).

Lemma rewrite_ge :
 forall x : R, forall xi : FF, forall n : Z, BND x xi ->
 rewrite_ge_helper xi n = true ->
 (x >= Float1 n)%R.
intros x xi n Hx Hb.
generalize (Fle2_correct _ _ Hb). clear Hb. intro H.
apply Rle_ge.
apply Rle_trans with (2 := proj1 Hx).
exact H.
Qed.

Definition rewrite_lt0_helper (xi : FF) :=
 Fneg (upper xi).

Lemma rewrite_lt0 :
 forall x : R, forall xi : FF, BND x xi ->
 rewrite_lt0_helper xi = true ->
 (x < 0)%R.
intros x xi Hx Hb.
generalize (Fneg_correct _ Hb). clear Hb. intro H.
apply Rle_lt_trans with (1 := proj2 Hx).
exact H.
Qed.

Definition rewrite_le0_helper (xi : FF) :=
 Fneg0 (upper xi).

Lemma rewrite_le0 :
 forall x : R, forall xi : FF, BND x xi ->
 rewrite_le0_helper xi = true ->
 (x <= 0)%R.
intros x xi Hx Hb.
generalize (Fneg0_correct _ Hb). clear Hb. intro H.
apply Rle_trans with (1 := proj2 Hx).
exact H.
Qed.

Definition rewrite_gt0_helper (xi : FF) :=
 Fpos (lower xi).

Lemma rewrite_gt0 :
 forall x : R, forall xi : FF, BND x xi ->
 rewrite_gt0_helper xi = true ->
 (x > 0)%R.
intros x xi Hx Hb.
generalize (Fpos_correct _ Hb). clear Hb. intro H.
unfold Rgt.
apply Rlt_le_trans with (2 := proj1 Hx).
exact H.
Qed.

Definition rewrite_ge0_helper (xi : FF) :=
 Fpos0 (lower xi).

Lemma rewrite_ge0 :
 forall x : R, forall xi : FF, BND x xi ->
 rewrite_ge0_helper xi = true ->
 (x >= 0)%R.
intros x xi Hx Hb.
generalize (Fpos0_correct _ Hb). clear Hb. intro H.
apply Rle_ge.
apply Rle_trans with (2 := proj1 Hx).
exact H.
Qed.

End Gappa_user.
