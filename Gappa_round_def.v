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

Definition good_rdir (rdir: rnd_record -> Z -> bool) :=
 forall m : N, forall e : Z,
 rdir (rnd_record_mk m false false) e = false /\
 (rdir (rnd_record_mk m false true) e = false \/ rdir (rnd_record_mk m true false) e = true) /\
 (rdir (rnd_record_mk m true false) e = false \/ rdir (rnd_record_mk m true true) e = true).

Record round_dir : Set := round_dir_mk {
 rpos : rnd_record -> Z -> bool ;
 rneg : rnd_record -> Z -> bool ;
 rpos_good : good_rdir rpos ;
 rneg_good : good_rdir rneg
}.

Definition rndZR (r : rnd_record) (_ : Z) : bool :=
 false.

Lemma rndZR_good : good_rdir rndZR.
unfold good_rdir, rndZR. simpl.
intuition.
Qed.

Definition rndAW (r : rnd_record) (_ : Z) : bool :=
 rnd_r r || rnd_s r.

Lemma rndAW_good : good_rdir rndAW.
unfold good_rdir, rndAW. simpl.
intuition.
Qed.

Definition rndNE (r : rnd_record) (_ : Z) : bool :=
 rnd_r r && (rnd_s r || negb (is_even (rnd_m r))).

Lemma rndNE_good : good_rdir rndNE.
unfold good_rdir, rndNE. simpl.
intuition.
Qed.

Definition rndNO (r : rnd_record) (_ : Z) : bool :=
 rnd_r r && (rnd_s r || is_even (rnd_m r)).

Lemma rndNO_good : good_rdir rndNO.
unfold good_rdir, rndNO. simpl.
intuition.
Qed.

Definition rndNZ (r : rnd_record) (_ : Z) : bool :=
 rnd_r r && rnd_s r.

Lemma rndNZ_good : good_rdir rndNZ.
unfold good_rdir, rndNZ. simpl.
intuition.
Qed.

Definition rndNA (r : rnd_record) (_ : Z) : bool :=
 rnd_r r.

Lemma rndNA_good : good_rdir rndNA.
unfold good_rdir, rndNA. simpl.
intuition.
Qed.

Definition rndOD (r : rnd_record) (_ : Z) : bool :=
 (rnd_r r || rnd_s r) && is_even (rnd_m r).

Lemma rndOD_good : good_rdir rndOD.
unfold good_rdir, rndOD. simpl.
intros.
case (is_even m) ; intuition.
Qed.

Definition roundZR := round_dir_mk rndZR rndZR rndZR_good rndZR_good.
Definition roundAW := round_dir_mk rndAW rndAW rndAW_good rndAW_good.
Definition roundUP := round_dir_mk rndAW rndZR rndAW_good rndZR_good.
Definition roundDN := round_dir_mk rndZR rndAW rndZR_good rndAW_good.
Definition roundOD := round_dir_mk rndOD rndOD rndOD_good rndOD_good.
Definition roundNE := round_dir_mk rndNE rndNE rndNE_good rndNE_good.
Definition roundNO := round_dir_mk rndNO rndNO rndNO_good rndNO_good.
Definition roundNZ := round_dir_mk rndNZ rndNZ rndNZ_good rndNZ_good.
Definition roundNA := round_dir_mk rndNA rndNA rndNA_good rndNA_good.
Definition roundNU := round_dir_mk rndNA rndNZ rndNA_good rndNZ_good.
Definition roundND := round_dir_mk rndNZ rndNA rndNZ_good rndNA_good.

End Gappa_round_def.
