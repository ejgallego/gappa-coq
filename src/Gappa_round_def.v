Require Import Bool.
Require Import ZArith.

Section Gappa_round_def.

Record rnd_record : Set := rnd_record_mk {
  rnd_m : N ;
  rnd_r : bool ;
  rnd_s : bool
}.

Definition is_even (n : N) :=
 match n with
 | N0 => true
 | Npos (xO _) => true
 | _ => false
 end.

Definition good_rdir (rdir: rnd_record -> bool) :=
 forall m : N,
 rdir (rnd_record_mk m false false) = false /\
 (rdir (rnd_record_mk m false true) = false \/ rdir (rnd_record_mk m true false) = true) /\
 (rdir (rnd_record_mk m true false) = false \/ rdir (rnd_record_mk m true true) = true).

Record round_dir : Set := round_dir_mk {
 rpos : rnd_record -> bool ;
 rneg : rnd_record -> bool ;
 rpos_good : good_rdir rpos ;
 rneg_good : good_rdir rneg
}.

Definition GrndZR (r : rnd_record) : bool :=
 false.

Lemma GrndZR_good : good_rdir GrndZR.
unfold good_rdir, GrndZR. simpl.
intuition.
Qed.

Definition GrndAW (r : rnd_record) : bool :=
 rnd_r r || rnd_s r.

Lemma GrndAW_good : good_rdir GrndAW.
unfold good_rdir, GrndAW. simpl.
intuition.
Qed.

Definition GrndNE (r : rnd_record) : bool :=
 rnd_r r && (rnd_s r || negb (is_even (rnd_m r))).

Lemma GrndNE_good : good_rdir GrndNE.
unfold good_rdir, GrndNE. simpl.
intuition.
Qed.

Definition GrndNO (r : rnd_record) : bool :=
 rnd_r r && (rnd_s r || is_even (rnd_m r)).

Lemma GrndNO_good : good_rdir GrndNO.
unfold good_rdir, GrndNO. simpl.
intuition.
Qed.

Definition GrndNZ (r : rnd_record) : bool :=
 rnd_r r && rnd_s r.

Lemma GrndNZ_good : good_rdir GrndNZ.
unfold good_rdir, GrndNZ. simpl.
intuition.
Qed.

Definition GrndNA (r : rnd_record) : bool :=
 rnd_r r.

Lemma GrndNA_good : good_rdir GrndNA.
unfold good_rdir, GrndNA. simpl.
intuition.
Qed.

Definition GrndOD (r : rnd_record) : bool :=
 (rnd_r r || rnd_s r) && is_even (rnd_m r).

Lemma GrndOD_good : good_rdir GrndOD.
unfold good_rdir, GrndOD. simpl.
intros.
case (is_even m) ; intuition.
Qed.

Definition roundZR := round_dir_mk GrndZR GrndZR GrndZR_good GrndZR_good.
Definition roundAW := round_dir_mk GrndAW GrndAW GrndAW_good GrndAW_good.
Definition roundUP := round_dir_mk GrndAW GrndZR GrndAW_good GrndZR_good.
Definition roundDN := round_dir_mk GrndZR GrndAW GrndZR_good GrndAW_good.
Definition roundOD := round_dir_mk GrndOD GrndOD GrndOD_good GrndOD_good.
Definition roundNE := round_dir_mk GrndNE GrndNE GrndNE_good GrndNE_good.
Definition roundNO := round_dir_mk GrndNO GrndNO GrndNO_good GrndNO_good.
Definition roundNZ := round_dir_mk GrndNZ GrndNZ GrndNZ_good GrndNZ_good.
Definition roundNA := round_dir_mk GrndNA GrndNA GrndNA_good GrndNA_good.
Definition roundNU := round_dir_mk GrndNA GrndNZ GrndNA_good GrndNZ_good.
Definition roundND := round_dir_mk GrndNZ GrndNA GrndNZ_good GrndNA_good.

End Gappa_round_def.
