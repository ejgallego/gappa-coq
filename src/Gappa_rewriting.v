Require Import Reals.
Require Import Gappa_common.

Theorem bnd_rewrite :
  forall a b : R, forall zi : FF,
  a = b -> BND b zi -> BND a zi.
Proof.
intros a b zi E Hz.
now rewrite E.
Qed.

Theorem abs_rewrite :
  forall a b : R, forall zi : FF,
  a = b -> ABS b zi -> ABS a zi.
Proof.
intros a b zi E Hz.
now rewrite E.
Qed.

Theorem fix_rewrite :
  forall a b : R, forall zn : Z,
  a = b -> FIX b zn -> FIX a zn.
Proof.
intros a b zn E Hz.
now rewrite E.
Qed.

Theorem flt_rewrite :
  forall a b : R, forall zn : positive,
  a = b -> FLT b zn -> FLT a zn.
Proof.
intros a b zn E Hz.
now rewrite E.
Qed.

Theorem nzr_rewrite :
  forall a b : R,
  a = b -> NZR b -> NZR a.
Proof.
intros a b E Hz.
now rewrite E.
Qed.

Theorem rel_rewrite_1 :
  forall a b c : R, forall zi : FF,
  a = b -> REL b c zi -> REL a c zi.
Proof.
intros a b c zi E Hz.
now rewrite E.
Qed.

Theorem rel_rewrite_2 :
  forall a b c : R, forall zi : FF,
  a = b -> REL c b zi -> REL c a zi.
Proof.
intros a b c zi E Hz.
now rewrite E.
Qed.

Theorem eql_trans :
  forall a b c : R,
  a = b -> b = c -> a = c.
Proof.
intros a b c H1 H2.
now rewrite H1.
Qed.

Theorem opp_mibs :
  forall a b : R, forall zi : FF,
  BND (-(a - b)) zi ->
  BND (-a - -b) zi.
Proof.
intros a b zi Hz.
now replace (-a - -b)%R with (-(a - b))%R by ring.
Qed.

Theorem opp_xibu :
  forall a : R, forall zi : FF,
  BND (-(-a)) zi ->
  BND a zi.
Proof.
intros a zi Hz.
now rewrite <- (Ropp_involutive a).
Qed.

Theorem add_xals :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + (c + b)) zi ->
 BND (a + b) zi.
Proof.
intros a b c zi Hz.
replace (a + b)%R with ((a - c) + (c + b))%R.
exact Hz.
ring.
Qed.

Theorem add_xars :
 forall a b c : R, forall zi : FF,
 BND ((a + c) + (b - c)) zi ->
 BND (a + b) zi.
Proof.
intros a b c zi Hz.
replace (a + b)%R with ((a + c) + (b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_xals :
 forall a b c : R, forall zi : FF,
 BND ((a - c) + (c - b)) zi ->
 BND (a - b) zi.
Proof.
intros a b c zi Hz.
replace (a - b)%R with ((a - c) + (c - b))%R.
exact Hz.
ring.
Qed.

Theorem sub_xars :
 forall a b c : R, forall zi : FF,
 BND ((a - c) - (b - c)) zi ->
 BND (a - b) zi.
Proof.
intros a b c zi Hz.
replace (a - b)%R with ((a - c) - (b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_xals :
 forall a b c : R, forall zi : FF,
 BND ((a - c) * b + c * b) zi ->
 BND (a * b) zi.
Proof.
intros a b c zi Hz.
replace (a * b)%R with ((a - c) * b + c * b)%R.
exact Hz.
ring.
Qed.

Theorem mul_xars :
 forall a b c : R, forall zi : FF,
 BND (a * (b - c) + a * c) zi ->
 BND (a * b) zi.
Proof.
intros a b c zi Hz.
replace (a * b)%R with (a * (b - c) + a * c)%R.
exact Hz.
ring.
Qed.

Theorem add_mibs :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) + (b - d)) zi ->
 BND ((a + b) - (c + d)) zi.
Proof.
intros a b c d zi Hz.
replace ((a + b) - (c + d))%R with ((a - c) + (b - d))%R.
exact Hz.
ring.
Qed.

Theorem add_fils :
 forall a b c : R, forall zi : FF,
 BND (b - c) zi ->
 BND ((a + b) - (a + c)) zi.
Proof.
intros a b c zi Hz.
replace ((a + b) - (a + c))%R with (b - c)%R.
exact Hz.
ring.
Qed.

Theorem add_firs :
 forall a b c : R, forall zi : FF,
 BND (a - c) zi ->
 BND ((a + b) - (c + b)) zi.
Proof.
intros a b c zi Hz.
replace ((a + b) - (c + b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem add_filq :
 forall a b c : R, forall zi : FF,
 NZR (a + c) -> BND ((b - c) / (a + c)) zi ->
 BND (((a + b) - (a + c)) / (a + c)) zi.
Proof.
intros a b c zi Hac Hz.
replace (((a + b) - (a + c)) / (a + c))%R with ((b - c) / (a + c))%R.
exact Hz.
field.
exact Hac.
Qed.

Theorem add_firq :
 forall a b c : R, forall zi : FF,
 NZR (c + b) -> BND ((a - c) / (c + b)) zi ->
 BND (((a + b) - (c + b)) / (c + b)) zi.
Proof.
intros a b c zi Hac Hz.
replace (((a + b) - (c + b)) / (c + b))%R with ((a - c) / (c + b))%R.
exact Hz.
field.
exact Hac.
Qed.

Theorem add_xilu :
  forall a b : R, forall zi : FF,
  BND ((a + b) - b) zi ->
  BND a zi.
Proof.
intros a b zi Hz.
replace a with (a + b - b)%R by ring.
exact Hz.
Qed.

Theorem add_xiru :
  forall a b : R, forall zi : FF,
  BND ((a + b) - a) zi ->
  BND b zi.
Proof.
intros a b zi Hz.
replace b with (a + b - a)%R by ring.
exact Hz.
Qed.

Theorem sub_mibs :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) + -(b - d)) zi ->
 BND ((a - b) - (c - d)) zi.
Proof.
intros a b c d zi Hz.
replace ((a - b) - (c - d))%R with ((a - c) + -(b - d))%R.
exact Hz.
ring.
Qed.

Theorem sub_fils :
 forall a b c : R, forall zi : FF,
 BND (-(b - c)) zi ->
 BND ((a - b) - (a - c)) zi.
Proof.
intros a b c zi Hz.
replace ((a - b) - (a - c))%R with (-(b - c))%R.
exact Hz.
ring.
Qed.

Theorem sub_firs :
 forall a b c : R, forall zi : FF,
 BND (a - c) zi ->
 BND ((a - b) - (c - b)) zi.
Proof.
intros a b c zi Hz.
replace ((a - b) - (c - b))%R with (a - c)%R.
exact Hz.
ring.
Qed.

Theorem sub_filq :
 forall a b c : R, forall zi : FF,
 NZR (a - c) -> BND (- ((b - c) / (a - c))) zi ->
 BND (((a - b) - (a - c)) / (a - c)) zi.
Proof.
intros a b c zi Hac Hz.
replace (((a - b) - (a - c)) / (a - c))%R with (-((b - c) / (a - c)))%R.
exact Hz.
field.
exact Hac.
Qed.

Theorem sub_firq :
 forall a b c : R, forall zi : FF,
 NZR (c - b) -> BND ((a - c) / (c - b)) zi ->
 BND (((a - b) - (c - b)) / (c - b)) zi.
Proof.
intros a b c zi Hac Hz.
replace (((a - b) - (c - b)) / (c - b))%R with ((a - c) / (c - b))%R.
exact Hz.
field.
exact Hac.
Qed.

Theorem mul_fils :
 forall a b c : R, forall zi : FF,
 BND (a * (b - c)) zi ->
 BND (a * b - a * c) zi.
Proof.
intros a b c zi Hz.
replace (a * b - a * c)%R with (a * (b - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_firs :
 forall a b c : R, forall zi : FF,
 BND ((a - c) * b) zi ->
 BND (a * b - c * b) zi.
Proof.
intros a b c zi Hz.
replace (a * b - c * b)%R with ((a - c) * b)%R.
exact Hz.
ring.
Qed.

Theorem mul_mars :
 forall a b c d : R, forall zi : FF,
 BND (a * (b - d) + (a - c) * d) zi ->
 BND (a * b - c * d) zi.
Proof.
intros a b c d zi Hz.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * d)%R.
exact Hz.
ring.
Qed.

Theorem mul_mals :
 forall a b c d : R, forall zi : FF,
 BND ((a - c) * b + c * (b - d)) zi ->
 BND (a * b - c * d) zi.
Proof.
intros a b c d zi Hz.
replace (a * b - c * d)%R with ((a - c) * b + c * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem mul_mabs :
 forall a b c d : R, forall zi : FF,
 BND (a * (b - d) + (a - c) * b - ((a - c) * (b - d))) zi ->
 BND (a * b - c * d) zi.
Proof.
intros a b c d zi Hz.
replace (a * b - c * d)%R with (a * (b - d) + (a - c) * b - ((a - c) * (b - d)))%R.
exact Hz.
ring.
Qed.

Theorem mul_mibs :
 forall a b c d : R, forall zi : FF,
 BND (c * (b - d) + (a - c) * d + (a - c) * (b - d)) zi ->
 BND (a * b - c * d) zi.
Proof.
intros a b c d zi Hz.
replace (a * b - c * d)%R with (c * (b - d) + (a - c) * d + (a - c) * (b - d))%R.
exact Hz.
ring.
Qed.

Theorem err_xalq :
 forall a b c : R, forall zi : FF,
 NZR b -> NZR c ->
 BND ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b)) zi ->
 BND ((a - b) / b) zi.
Proof.
intros a b c zi Hb Hc Hz.
replace ((a - b) / b)%R with ((a - c) / c + (c - b) / b + ((a - c) / c) * ((c - b) / b))%R.
exact Hz.
field.
exact (conj Hb Hc).
Qed.

Theorem mul_filq :
  forall a b c : R, forall zi : FF,
  REL b c zi ->
  REL (a * b) (a * c) zi.
Proof.
intros a b c zi (ze, (Hz1, Hz2)).
exists ze.
split.
exact Hz1.
rewrite Hz2.
apply sym_eq.
apply Rmult_assoc.
Qed.

Theorem mul_firq :
  forall a b c : R, forall zi : FF,
  REL a c zi ->
  REL (a * b) (c * b) zi.
Proof.
intros a b c zi (ze, (Hz1, Hz2)).
exists ze.
split.
exact Hz1.
rewrite Hz2.
ring.
Qed.

Theorem mul_xilu :
  forall a b : R, forall zi : FF,
  NZR b ->
  BND ((a * b) / b) zi ->
  BND a zi.
Proof.
intros a b zi Hb Hz.
replace a with (a * b / b)%R.
exact Hz.
now field.
Qed.

Theorem mul_xiru :
  forall a b : R, forall zi : FF,
  NZR a ->
  BND ((a * b) / a) zi ->
  BND b zi.
Proof.
intros a b zi Hb Hz.
replace b with (a * b / a)%R.
exact Hz.
now field.
Qed.

Theorem sqrt_mibs :
 forall a b : R, forall ai bi zi : FF,
 BND a ai -> BND b bi ->
 BND ((a - b) / (sqrt a + sqrt b)) zi ->
 Fpos0 (lower ai) && Fpos0 (lower bi) = true ->
 BND (sqrt a - sqrt b) zi.
Proof.
intros a b ai bi zi Ha Hb Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
assert (H3: (0 <= sqrt a)%R).
apply sqrt_positivity.
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
assert (H4: (0 <= sqrt b)%R).
apply sqrt_positivity.
apply Rle_trans with (1 := H2) (2 := proj1 Hb).
case (Rtotal_order (sqrt a + sqrt b) 0).
intro H. elim Rlt_not_le with (1 := H).
apply Rplus_le_le_0_compat ; assumption.
intros [H|H] ;
replace (sqrt a - sqrt b)%R with ((a - b) / (sqrt a + sqrt b))%R ;
try exact Hz.
assert (sqrt a = 0)%R.
apply Rle_antisym. 2: exact H3.
rewrite <- H.
pattern (sqrt a) at 1 ; rewrite <- (Rplus_0_r (sqrt a)).
apply Rplus_le_compat_l with (1 := H4).
rewrite H0 in H.
rewrite Rplus_0_l in H.
rewrite H. rewrite H0.
assert (a = 0)%R as ->.
  apply sqrt_eq_0 with (2 := H0).
  apply Rle_trans with (1 := H1) (2 := proj1 Ha).
assert (b = 0)%R as ->.
  apply sqrt_eq_0 with (2 := H).
  apply Rle_trans with (1 := H2) (2 := proj1 Hb).
rewrite Rminus_0_r.
unfold Rdiv.
apply Rmult_0_l.
replace (a - b)%R with (sqrt a * sqrt a - sqrt b * sqrt b)%R.
field.
now apply Rgt_not_eq.
repeat rewrite sqrt_def.
exact (refl_equal _).
apply Rle_trans with (1 := H2) (2 := proj1 Hb).
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
Qed.

Theorem sqrt_mibq :
 forall a b : R, forall ai bi zi : FF,
 BND a ai -> BND b bi ->
 BND (sqrt (1 + (a - b) / b) - 1) zi ->
 Fpos0 (lower ai) && Fpos (lower bi) = true ->
 BND ((sqrt a - sqrt b) / sqrt b) zi.
Proof.
intros a b ai bi zi Ha Hb Hz H.
generalize (andb_prop _ _ H). clear H. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fpos_correct _ H2). clear H2. intro H2.
replace ((sqrt a - sqrt b) / sqrt b)%R with (sqrt (1 + (a - b) / b) - 1)%R.
exact Hz.
replace (1 + (a - b) / b)%R with (a / b)%R.
rewrite sqrt_div.
field.
apply Rgt_not_eq.
unfold Rgt.
apply sqrt_lt_R0.
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
apply Rle_trans with (1 := H1) (2 := proj1 Ha).
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
field.
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (1 := H2) (2 := proj1 Hb).
Qed.

Theorem sqrt_xibu :
  forall a : R, forall ai zi : FF,
  BND a ai ->
  BND (sqrt a * sqrt a) zi ->
  Fpos0 (lower ai) = true ->
  BND a zi.
Proof.
intros a ai zi Ha Hz H.
generalize (Fpos0_correct _ H). clear H. intro H.
rewrite <- (sqrt_sqrt a).
exact Hz.
apply Rle_trans with (1 := H).
apply Ha.
Qed.

Theorem abs_mul_xx :
 forall a b : R, forall zi : FF,
 BND (Rabs a * Rabs b) zi ->
 BND (Rabs (a * b)) zi.
Proof.
intros a b zi Hz.
rewrite Rabs_mult.
exact Hz.
Qed.

Theorem val_xebs :
 forall a b : R, forall zi : FF,
 BND (b - (b - a)) zi ->
 BND a zi.
Proof.
intros a b zi Hz.
replace a with (b - (b - a))%R.
exact Hz.
ring.
Qed.

Theorem val_xabs :
 forall a b : R, forall zi : FF,
 BND (a + (b - a)) zi ->
 BND b zi.
Proof.
intros a b zi Hz.
replace b with (a + (b - a))%R.
exact Hz.
ring.
Qed.

Theorem div_mibq :
 forall a b c d : R, forall zi : FF,
 NZR b -> NZR c -> NZR d ->
 BND (((a - c) / c - (b - d) / d) / (1 + (b - d) / d)) zi ->
 BND ((a / b - c / d) / (c / d)) zi.
Proof.
intros a b c d zi Hb Hc Hd Hz.
replace ((a / b - c / d) / (c / d))%R with (((a - c) / c - (b - d) / d) / (1 + (b - d) / d))%R.
exact Hz.
field.
exact (conj Hd (conj Hb Hc)).
Qed.

Theorem div_xals :
 forall a b c : R, forall zi : FF,
 NZR c ->
 BND ((b - a) / c + a / c) zi ->
 BND (b / c) zi.
Proof.
intros a b c zi Hc Hz.
replace (b / c)%R with ((b - a) / c + a / c)%R.
exact Hz.
field.
exact Hc.
Qed.

Theorem div_firs :
  forall a b c : R, forall zi : FF,
  NZR b ->
  BND ((a - c) / b) zi ->
  BND (a / b - c / b) zi.
Proof.
intros a b c zi Hb Hz.
replace (a / b - c / b)%R with ((a - c) / b)%R.
exact Hz.
now field.
Qed.

Theorem div_firq :
  forall a b c : R, forall zi : FF,
  REL a c zi ->
  REL (a / b) (c / b) zi.
Proof.
intros a b c zi (ze, (Hz1, Hz2)).
exists ze.
split.
exact Hz1.
rewrite Hz2.
unfold Rdiv.
ring.
Qed.

Theorem div_fir :
 forall a b : R, forall zi : FF,
 NZR b ->
 BND a zi ->
 BND ((a * b) / b) zi.
Proof.
intros a b zi Hb Hz.
replace ((a * b) / b)%R with a.
exact Hz.
field.
exact Hb.
Qed.

Theorem div_fil :
 forall a b : R, forall zi : FF,
 NZR a ->
 BND b zi ->
 BND ((a * b) / a) zi.
Proof.
intros a b zi Hb Hz.
replace (( a * b) / a)%R with b.
exact Hz.
field.
exact Hb.
Qed.

Theorem div_xilu :
  forall a b : R, forall zi : FF,
  NZR b ->
  BND ((a / b) * b) zi ->
  BND a zi.
Proof.
intros a b zi Hb Hz.
replace a with (a / b * b)%R.
exact Hz.
now field.
Qed.

Theorem div_xiru :
  forall a b : R, forall zi : FF,
  NZR a -> NZR b ->
  BND (a / (a / b)) zi ->
  BND b zi.
Proof.
intros a b zi Ha Hb Hz.
replace b with (a / (a / b))%R.
exact Hz.
field.
now split.
Qed.

Theorem err_xabq :
 forall a b : R, forall zi : FF,
 NZR b -> BND (1 + (a - b) / b) zi ->
 BND (a / b) zi.
Proof.
intros a b zi Hb Hz.
replace (a / b)%R with (1 + (a - b) / b)%R.
exact Hz.
field.
exact Hb.
Qed.

Theorem err_fabq :
 forall a b : R, forall zi : FF,
 NZR b -> BND (a / b) zi ->
 BND (1 + (a - b) / b) zi.
Proof.
intros a b zi Hb Hz.
replace (1 + (a - b) / b)%R with (a / b)%R .
exact Hz.
field.
exact Hb.
Qed.

Theorem addf_1 :
  forall a b : R, forall zi : FF,
  NZR a -> NZR (a + b) -> BND (1 / (1 + b / a)) zi ->
  BND (a / (a + b)) zi.
Proof.
intros a b zi Ha Hab Hz.
replace (a / (a + b))%R with (1 / (1 + b / a))%R.
exact Hz.
field.
exact (conj Hab Ha).
Qed.

Theorem addf_2 :
  forall a b : R, forall zi : FF,
  NZR (a + b) -> BND (1 - b / (a + b)) zi ->
  BND (a / (a + b)) zi.
Proof.
intros a b zi Hab Hz.
replace (a / (a + b))%R with (1 - b / (a + b))%R.
exact Hz.
field.
exact Hab.
Qed.

Theorem addf_3 :
  forall a b : R, forall zi : FF,
  NZR a -> NZR (a - b) -> BND (1 / (1 - b / a)) zi ->
  BND (a / (a - b)) zi.
Proof.
intros a b zi Ha Hab Hz.
replace (a / (a - b))%R with (1 / (1 - b / a))%R.
exact Hz.
field.
exact (conj Hab Ha).
Qed.

Theorem addf_4 :
  forall a b : R, forall zi : FF,
  NZR (a - b) -> BND (1 + b / (a - b)) zi ->
  BND (a / (a - b)) zi.
Proof.
intros a b zi Hab Hz.
replace (a / (a - b))%R with (1 + b / (a - b))%R.
exact Hz.
field.
exact Hab.
Qed.

Theorem addf_5 :
  forall a b : R, forall zi : FF,
  NZR b -> NZR (a + b) -> BND (1 / (a / b + 1)) zi ->
  BND (b / (a + b)) zi.
Proof.
intros a b zi Hb Hab Hz.
replace (b / (a + b))%R with (1 / (a / b + 1))%R.
exact Hz.
field.
exact (conj Hab Hb).
Qed.

Theorem addf_6 :
  forall a b : R, forall zi : FF,
  NZR (a + b) -> BND (1 - a / (a + b)) zi ->
  BND (b / (a + b)) zi.
Proof.
intros a b zi Hab Hz.
replace (b / (a + b))%R with (1 - a / (a + b))%R.
exact Hz.
field.
exact Hab.
Qed.

Theorem addf_7 :
  forall a b : R, forall zi : FF,
  NZR b -> NZR (a - b) -> BND (1 / (a / b - 1)) zi ->
  BND (b / (a - b)) zi.
Proof.
intros a b zi Hb Hab Hz.
replace (b / (a - b))%R with (1 / (a / b - 1))%R.
exact Hz.
field.
exact (conj Hab Hb).
Qed.

Theorem addf_8 :
  forall a b : R, forall zi : FF,
  NZR (a - b) -> BND (a / (a - b) - 1) zi ->
  BND (b / (a - b)) zi.
Proof.
intros a b zi Hab Hz.
replace (b / (a - b))%R with (a / (a - b) - 1)%R.
exact Hz.
field.
exact Hab.
Qed.

Theorem opp_fibq :
  forall a b : R, forall zi : FF,
  REL a b zi ->
  REL (-a) (-b) zi.
Proof.
intros a b zi (ze, (Hz1, Hz2)).
exists ze.
split.
exact Hz1.
rewrite Hz2.
apply sym_eq.
apply Ropp_mult_distr_l_reverse.
Qed.

Theorem opp_fibe :
  forall a b : R,
  a = b -> (-a = -b)%R.
Proof.
intros a b H.
now rewrite H.
Qed.

Theorem add_file :
  forall a b c : R,
  b = c -> (a + b = a + c)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem add_fire :
  forall a b c : R,
  a = c -> (a + b = c + b)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem sub_file :
  forall a b c : R,
  b = c -> (a - b = a - c)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem sub_fire :
  forall a b c : R,
  a = c -> (a - b = c - b)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem mul_file :
  forall a b c : R,
  b = c -> (a * b = a * c)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem mul_fire :
  forall a b c : R,
  a = c -> (a * b = c * b)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem div_file :
  forall a b c : R,
  b = c -> (a / b = a / c)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.

Theorem div_fire :
  forall a b c : R,
  a = c -> (a / b = c / b)%R.
Proof.
intros a b c H.
now rewrite H.
Qed.
