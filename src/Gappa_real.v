Require Import Reals.

Section Gappa_real.

Theorem IRsubset :
 forall yl yu zl zu : R,
 (zl <= yl)%R -> (yu <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= y <= zu)%R.
intros yl yu zl zu Hzl Hzu y (Hyl,Hyu).
split.
apply Rle_trans with (1 := Hzl) (2 := Hyl).
apply Rle_trans with (1 := Hyu) (2 := Hzu).
Qed.

Theorem IRplus :
 forall xl xu yl yu zl zu : R,
 (zl <= xl + yl)%R -> (xu + yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x + y <= zu)%R.
intros xl xu yl yu zl zu Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rplus_le_compat with (1 := Hxl) (2 := Hyl).
apply Rplus_le_compat with (1 := Hxu) (2 := Hyu).
Qed.

Theorem IRopp :
 forall yl yu zl zu : R,
 (zl <= -yu)%R -> (-yl <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= -y <= zu)%R.
intros yl yu zl zu Hzl Hzu y (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Ropp_le_contravar with (1 := Hyu).
apply Ropp_le_contravar with (1 := Hyl).
Qed.

Theorem IRminus :
 forall xl xu yl yu zl zu : R,
 (zl <= xl - yu)%R -> (xu - yl <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x - y <= zu)%R.
unfold Rminus.
intros xl xu yl yu zl zu Hzl Hzu x y Hx Hy.
apply IRplus with (1 := Hzl) (2 := Hzu) (3 := Hx).
apply IRopp with (3 := Hy) ; auto with real.
Qed.

Lemma monotony_1p :
 forall a x y : R, (0 <= a)%R -> (x <= y)%R -> (a * x <= a * y)%R.
auto with real.
Qed.

Lemma monotony_2p :
 forall a x y : R, (0 <= a)%R -> (x <= y)%R -> (x * a <= y * a)%R.
auto with real.
Qed.

Lemma monotony_1n :
 forall a x y : R, (a <= 0)%R -> (x <= y)%R -> (a * y <= a * x)%R.
auto with real.
Qed.

Lemma monotony_2n :
 forall a x y : R, (a <= 0)%R -> (x <= y)%R -> (y * a <= x * a)%R.
intros a x y Ha H.
rewrite Rmult_comm. rewrite (Rmult_comm x).
apply Rge_le.
auto with real.
Qed.

Theorem IRmult_pp :
 forall xl xu yl yu zl zu : R,
 (0 <= xl)%R -> (0 <= yl)%R ->
 (zl <= xl * yl)%R -> (xu * yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (xl * y)%R.
exact (monotony_1p _ _ _ Hx Hyl).
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hy Hyl) Hxl).
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hx Hxl) Hyu).
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hy (Rle_trans _ _ _ Hyl Hyu)) Hxu).
Qed.

Theorem IRmult_po :
 forall xl xu yl yu zl zu : R,
 (0 <= xl)%R -> (yl <= 0)%R -> (0 <= yu)%R ->
 (zl <= xu * yl)%R -> (xu * yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy1 Hy2 Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (x * yl)%R.
exact (monotony_2n _ _ _ Hy1 Hxu).
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hx Hxl) Hyl).
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hx Hxl) Hyu).
exact (monotony_2p _ _ _ Hy2 Hxu).
Qed.

Theorem IRmult_pn :
 forall xl xu yl yu zl zu : R,
 (0 <= xl)%R -> (yu <= 0)%R ->
 (zl <= xu * yl)%R -> (xl * yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (xu * y)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hx (Rle_trans _ _ _ Hxl Hxu)) Hyl).
exact (monotony_2n _ _ _ (Rle_trans _ _ _ Hyu Hy) Hxu).
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hx Hxl) Hyu).
exact (monotony_2n _ _ _ Hy Hxl).
Qed.

Theorem IRmult_op :
 forall xl xu yl yu zl zu : R,
 (xl <= 0)%R -> (0 <= xu)%R -> (0 <= yl)%R ->
 (zl <= xl * yu)%R -> (xu * yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx1 Hx2 Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (xl * y)%R.
exact (monotony_1n _ _ _ Hx1 Hyu).
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hy Hyl) Hxl).
apply Rle_trans with (xu * y)%R.
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hy Hyl) Hxu).
exact (monotony_1p _ _ _ Hx2 Hyu).
Qed.

Theorem IRmult_oo :
 forall xl xu yl yu zl zu : R,
 (xl <= 0)%R -> (0 <= xu)%R -> (yl <= 0)%R -> (0 <= yu)%R ->
 (zl <= xu * yl)%R -> (zl <= xl * yu)%R ->
 (xl * yl <= zu)%R -> (xu * yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx1 Hx2 Hy1 Hy2 Hzl1 Hzl2 Hzu1 Hzu2 x y (Hxl,Hxu) (Hyl,Hyu).
case (Rlt_le_dec 0 x) ; intro H.
generalize (Rlt_le _ _ H). clear H. intro H.
split.
apply Rle_trans with (1 := Hzl1).
apply Rle_trans with (x * yl)%R.
exact (monotony_2n _ _ _ Hy1 Hxu).
exact (monotony_1p _ _ _ H Hyl).
apply Rle_trans with (2 := Hzu2).
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ H Hyu).
exact (monotony_2p _ _ _ Hy2 Hxu).
split.
apply Rle_trans with (1 := Hzl2).
apply Rle_trans with (x * yu)%R.
exact (monotony_2p _ _ _ Hy2 Hxl).
exact (monotony_1n _ _ _ H Hyu).
apply Rle_trans with (2 := Hzu1).
apply Rle_trans with (x * yl)%R.
exact (monotony_1n _ _ _ H Hyl).
exact (monotony_2n _ _ _ Hy1 Hxl).
Qed.

Theorem IRmult_on :
 forall xl xu yl yu zl zu : R,
 (xl <= 0)%R -> (0 <= xu)%R -> (yu <= 0)%R ->
 (zl <= xu * yl)%R -> (xl * yl <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx1 Hx2 Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (xu * y)%R.
exact (monotony_1p _ _ _ Hx2 Hyl).
exact (monotony_2n _ _ _ (Rle_trans _ _ _ Hyu Hy) Hxu).
apply Rle_trans with (xl * y)%R.
exact (monotony_2n _ _ _ (Rle_trans _ _ _ Hyu Hy) Hxl).
exact (monotony_1n _ _ _ Hx1 Hyl).
Qed.

Theorem IRmult_np :
 forall xl xu yl yu zl zu : R,
 (xu <= 0)%R -> (0 <= yl)%R ->
 (zl <= xl * yu)%R -> (xu * yl <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (x * yu)%R.
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hy (Rle_trans _ _ _ Hyl Hyu)) Hxl).
exact (monotony_1n _ _ _ (Rle_trans _ _ _ Hxu Hx) Hyu).
apply Rle_trans with (xu * y)%R.
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hy Hyl) Hxu).
exact (monotony_1n _ _ _ Hx Hyl).
Qed.

Theorem IRmult_no :
 forall xl xu yl yu zl zu : R,
 (xu <= 0)%R -> (yl <= 0)%R -> (0 <= yu)%R ->
 (zl <= xl * yu)%R -> (xl * yl <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy1 Hy2 Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (x * yu)%R.
exact (monotony_2p _ _ _ Hy2 Hxl).
exact (monotony_1n _ _ _ (Rle_trans _ _ _ Hxu Hx) Hyu).
apply Rle_trans with (x * yl)%R.
exact (monotony_1n _ _ _ (Rle_trans _ _ _ Hxu Hx) Hyl).
exact (monotony_2n _ _ _ Hy1 Hxl).
Qed.

Theorem IRmult_nn :
 forall xl xu yl yu zl zu : R,
 (xu <= 0)%R -> (yu <= 0)%R ->
 (zl <= xu * yu)%R -> (xl * yl <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_trans with (xu * y)%R.
exact (monotony_1n _ _ _ Hx Hyu).
exact (monotony_2n _ _ _ (Rle_trans _ _ _ Hyu Hy) Hxu).
apply Rle_trans with (xl * y)%R.
exact (monotony_2n _ _ _ (Rle_trans _ _ _ Hyu Hy) Hxl).
exact (monotony_1n _ _ _ (Rle_trans _ _ _ (Rle_trans _ _ _ Hxl Hxu) Hx) Hyl).
Qed.

Inductive interval_sign (xl xu : R) : Set :=
  | Nsign : (xu <= 0)%R -> interval_sign xl xu
  | Msign : (xl <= 0)%R -> (0 <= xu)%R -> interval_sign xl xu
  | Psign : (0 <= xl)%R -> interval_sign xl xu.

Lemma interval_sign_correct :
 forall xl xu : R, (xl <= xu)%R -> interval_sign xl xu.
intros xl xu H.
case (Rlt_le_dec xu 0); intro H0.
exact (Nsign _ _ (Rlt_le _ _ H0)).
case (Rlt_le_dec xl 0); intro H1.
exact (Msign _ _ (Rlt_le _ _ H1) H0).
exact (Psign _ _ H1).
Qed.

Lemma Rmin_trans :
 forall a b c : R, (c <= Rmin a b)%R -> (c <= a)%R /\ (c <= b)%R.
intros a b c H.
split.
exact (Rle_trans _ _ _ H (Rmin_l _ _)).
exact (Rle_trans _ _ _ H (Rmin_r _ _)).
Qed.

Lemma Rmax_trans :
 forall a b c : R, (Rmax a b <= c)%R -> (a <= c)%R /\ (b <= c)%R.
intros a b c H.
split.
exact (Rle_trans _ _ _ (RmaxLess1 _ _) H).
exact (Rle_trans _ _ _ (RmaxLess2 _ _) H).
Qed.

Lemma IRmult_minmax :
 forall xl xu yl yu zl zu : R,
 (zl <= Rmin (Rmin (xl * yl) (xl * yu)) (Rmin (xu * yl) (xu * yu)))%R ->
 (Rmax (Rmax (xl * yl) (xl * yu)) (Rmax (xu * yl) (xu * yu)) <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu Hzl Hzu x y Hx Hy.
decompose [and] (Rmin_trans _ _ _ Hzl).
decompose [and] (Rmin_trans _ _ _ H).
decompose [and] (Rmin_trans _ _ _ H0).
clear Hzl H H0.
decompose [and] (Rmax_trans _ _ _ Hzu).
decompose [and] (Rmax_trans _ _ _ H).
decompose [and] (Rmax_trans _ _ _ H0).
clear Hzu H H0.
case (interval_sign_correct _ _ (Rle_trans _ _ _ (proj1 Hx) (proj2 Hx))) ;
case (interval_sign_correct _ _ (Rle_trans _ _ _ (proj1 Hy) (proj2 Hy))) ; intros.
apply IRmult_nn with xl xu yl yu ; assumption.
apply IRmult_no with xl xu yl yu ; assumption.
apply IRmult_np with xl xu yl yu ; assumption.
apply IRmult_on with xl xu yl yu ; assumption.
apply IRmult_oo with xl xu yl yu ; assumption.
apply IRmult_op with xl xu yl yu ; assumption.
apply IRmult_pn with xl xu yl yu ; assumption.
apply IRmult_po with xl xu yl yu ; assumption.
apply IRmult_pp with xl xu yl yu ; assumption.
Qed.

Lemma Rle_Rinv_pos :
 forall x y : R,
 (0 < x)%R -> (x <= y)%R ->
 (/y <= /x)%R.
intros x y Hx H.
apply Rle_Rinv with (1 := Hx) (3 := H).
apply Rlt_le_trans with (1 := Hx) (2 := H).
Qed.

Lemma Rle_Rinv_neg :
 forall x y : R,
 (y < 0)%R -> (x <= y)%R ->
 (/y <= /x)%R.
intros x y Hy H.
apply Ropp_le_cancel.
repeat rewrite Ropp_inv_permute.
apply Rle_Rinv_pos.
apply Ropp_0_gt_lt_contravar with (1 := Hy).
apply Ropp_le_contravar with (1 := H).
exact (Rlt_not_eq _ _ Hy).
exact (Rlt_not_eq _ _ (Rle_lt_trans _ _ _ H Hy)).
Qed.

Lemma IRinv_p :
 forall yl yu zl zu : R,
 (0 < yl)%R ->
 (zl <= /yu)%R -> (/yl <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= /y <= zu)%R.
intros yl yu zl zu Hy Hzl Hzu y (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
apply Rle_Rinv_pos with (2 := Hyu).
exact (Rlt_le_trans _ _ _ Hy Hyl).
exact (Rle_Rinv_pos _ _ Hy Hyl).
Qed.

Lemma IRinv_n :
 forall yl yu zl zu,
 (yu < 0)%R ->
 (zl <= /yu)%R -> (/yl <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= /y <= zu)%R.
intros yl yu zl zu Hy Hzl Hzu y (Hyl,Hyu).
apply IRsubset with (1 := Hzl) (2 := Hzu).
split.
exact (Rle_Rinv_neg _ _ Hy Hyu).
apply Rle_Rinv_neg with (2 := Hyl).
exact (Rle_lt_trans _ _ _ Hyu Hy).
Qed.

Lemma IRinv_disj :
 forall yl yu zl zu : R,
 (yu < 0)%R \/ (0 < yl)%R ->
 (zl <= /yu)%R -> (/yl <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= /y <= zu)%R.
intros yl yu zl zu [Hy2|Hy1] Hzl Hzu y Hy.
exact (IRinv_n _ _ _ _ Hy2 Hzl Hzu _ Hy).
exact (IRinv_p _ _ _ _ Hy1 Hzl Hzu _ Hy).
Qed.

Lemma IRdiv_minmax :
 forall xl xu yl yu zl zu : R,
 (yu < 0)%R \/ (yl > 0)%R ->
 (zl <= Rmin (Rmin (xl / yu) (xl / yl)) (Rmin (xu / yu) (xu / yl)))%R ->
 (Rmax (Rmax (xl / yu) (xl / yl)) (Rmax (xu / yu) (xu / yl)) <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
unfold Rdiv.
intros xl xu yl yu zl zu H Hzl Hzu x y Hx Hy.
apply (IRmult_minmax _ _ (/yu) (/yl) _ _ Hzl Hzu _ (/y) Hx).
apply (IRinv_disj _ _ (/yu) (/yl) H) with (3 := Hy) ; auto with real.
Qed.

Lemma IRdiv_aux_p :
 forall yl yu y : R,
 (0 < yl)%R -> (yl <= y <= yu)%R ->
 (0 <= / yl)%R /\ (0 <= / yu)%R /\ (yl <> 0)%R /\ (yu <> 0)%R /\ (/ yu <= /y <= / yl)%R.
intros yl yu y Hyl Hy.
split. left.
apply Rinv_0_lt_compat.
exact Hyl.
split. left.
apply Rinv_0_lt_compat.
exact (Rlt_le_trans _ _ _ Hyl (Rle_trans _ _ _ (proj1 Hy) (proj2 Hy))).
split.
apply Rgt_not_eq.
exact Hyl.
split.
apply Rgt_not_eq.
exact (Rlt_le_trans _ _ _ Hyl (Rle_trans _ _ _ (proj1 Hy) (proj2 Hy))).
split.
exact (Rle_Rinv_pos _ _ (Rlt_le_trans _ _ _ Hyl (proj1 Hy)) (proj2 Hy)).
exact (Rle_Rinv_pos _ _ Hyl (proj1 Hy)).
Qed.

Theorem IRdiv_pp :
 forall xl xu yl yu zl zu : R,
 (0 <= xl)%R ->
 (0 < yl)%R ->
 (yu * zl <= xl)%R ->
 (xu <= yl * zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu Hxl Hyl Hzl Hzu x y Hx Hy.
generalize (IRdiv_aux_p _ _ _ Hyl Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply IRmult_pp with (1 := Hxl) (2 := Hy2) (5 := Hx) (6 := Hy5).
replace zl with (yu * zl * / yu)%R.
exact (monotony_2p _ _ _ Hy2 Hzl).
field. exact Hy4.
replace zu with (yl * zu * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzu).
field. exact Hy3.
Qed.

Theorem IRdiv_op :
 forall xl xu yl yu zl zu : R,
 (xl <= 0)%R ->
 (0 <= xu)%R ->
 (0 < yl)%R ->
 (yl * zl <= xl)%R ->
 (xu <= yl * zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu Hxl Hxu Hyl Hzl Hzu x y Hx Hy.
generalize (IRdiv_aux_p _ _ _ Hyl Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply IRmult_op with (1 := Hxl) (2 := Hxu) (3 := Hy2) (6 := Hx) (7 := Hy5).
replace zl with (yl * zl * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzl).
field. exact Hy3.
replace zu with (yl * zu * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzu).
field. exact Hy3.
Qed.

Theorem IRdiv_np :
 forall xl xu yl yu zl zu : R,
 (xu <= 0)%R ->
 (0 < yl)%R ->
 (yl * zl <= xl)%R ->
 (xu <= yu * zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu Hxu Hyl Hzl Hzu x y Hx Hy.
generalize (IRdiv_aux_p _ _ _ Hyl Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply IRmult_np with (1 := Hxu) (2 := Hy2) (5 := Hx) (6 := Hy5).
replace zl with (yl * zl * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzl).
field. exact Hy3.
replace zu with (yu * zu * / yu)%R.
exact (monotony_2p _ _ _ Hy2 Hzu).
field. exact Hy4.
Qed.

Lemma IRdiv_aux_n :
 forall yl yu y : R,
 (yu < 0)%R -> (yl <= y <= yu)%R ->
 (/ yl <= 0)%R /\ (/ yu <= 0)%R /\ (yl <> 0)%R /\ (yu <> 0)%R /\ (/ yu <= /y <= / yl)%R.
intros yl yu y Hyu Hy.
split. left.
apply Rinv_lt_0_compat.
exact (Rle_lt_trans _ _ _ (Rle_trans _ _ _ (proj1 Hy) (proj2 Hy)) Hyu).
split. left.
apply Rinv_lt_0_compat.
exact Hyu.
split.
apply Rlt_not_eq.
exact (Rle_lt_trans _ _ _ (Rle_trans _ _ _ (proj1 Hy) (proj2 Hy)) Hyu).
split.
apply Rlt_not_eq.
exact Hyu.
split.
exact (Rle_Rinv_neg _ _ Hyu (proj2 Hy)).
exact (Rle_Rinv_neg _ _ (Rle_lt_trans _ _ _ (proj2 Hy) Hyu) (proj1 Hy)).
Qed.

Theorem IRdiv_pn :
 forall xl xu yl yu zl zu : R,
 (0 <= xl)%R ->
 (yu < 0)%R ->
 (xu <= yu * zl)%R ->
 (yl * zu <= xl)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu Hxl Hyu Hzl Hzu x y Hx Hy.
generalize (IRdiv_aux_n _ _ _ Hyu Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply IRmult_pn with (1 := Hxl) (2 := Hy1) (5 := Hx) (6 := Hy5).
replace zl with (yu * zl * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzl).
field. exact Hy4.
replace zu with (yl * zu * / yl)%R.
exact (monotony_2n _ _ _ Hy1 Hzu).
field. exact Hy3.
Qed.

Theorem IRdiv_on :
 forall xl xu yl yu zl zu : R,
 (xl <= 0)%R ->
 (0 <= xu)%R ->
 (yu < 0)%R ->
 (xu <= yu * zl)%R ->
 (yu * zu <= xl)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu Hxl Hxu Hyu Hzl Hzu x y Hx Hy.
generalize (IRdiv_aux_n _ _ _ Hyu Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply IRmult_on with (1 := Hxl) (2 := Hxu) (3 := Hy1) (6 := Hx) (7 := Hy5).
replace zl with (yu * zl * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzl).
field. exact Hy4.
replace zu with (yu * zu * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzu).
field. exact Hy4.
Qed.

Theorem IRdiv_nn :
 forall xl xu yl yu zl zu : R,
 (xu <= 0)%R ->
 (yu < 0)%R ->
 (xu <= yl * zl)%R ->
 (yu * zu <= xl)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu Hxu Hyu Hzl Hzu x y Hx Hy.
generalize (IRdiv_aux_n _ _ _ Hyu Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply IRmult_nn with (1 := Hxu) (2 := Hy1) (5 := Hx) (6 := Hy5).
replace zl with (yl * zl * / yl)%R.
exact (monotony_2n _ _ _ Hy1 Hzl).
field. exact Hy3.
replace zu with (yu * zu * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzu).
field. exact Hy4.
Qed.

Theorem IRsquare_o :
 forall yl yu zl zu : R,
 (yl <= 0)%R -> (0 <= yu)%R -> (zl <= 0)%R ->
 (yl * yl <= zu)%R -> (yu * yu <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= y * y <= zu)%R.
intros yl yu zl zu Hy1 Hy2 Hzl Hzu1 Hzu2 y (Hyl,Hyu).
split.
fold (Rsqr y).
apply Rle_trans with 0%R ; auto with real.
case (Rlt_le_dec 0 y) ; intro H.
generalize (Rlt_le _ _ H). clear H. intro H.
apply Rle_trans with (yu * yu)%R ; auto with real.
apply Rle_trans with (2 := Hzu1).
apply Rle_trans with (y * yl)%R.
exact (monotony_1n _ _ _ H Hyl).
exact (monotony_2n _ _ _ Hy1 Hyl).
Qed.

Theorem IRsqrt :
 forall yl yu zl zu : R,
 match (Rlt_le_dec 0 zl) with
 | left _ => (zl * zl <= yl)%R
 | right _ => (0 <= yl)%R
 end -> (0 <= zu)%R -> (yu <= zu * zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= sqrt y <= zu)%R.
intros yl yu zl zu.
case (Rlt_le_dec 0 zl) ; intros Hzl1 Hzl2 Hzu1 Hzu2 y (Hyl,Hyu).
assert (H1: (zl * zl <= y)%R).
apply Rle_trans with (1 := Hzl2) (2 := Hyl).
assert (H2: (0 <= y)%R).
apply Rle_trans with (2 := H1).
exact (Rle_0_sqr _).
split.
rewrite <- (sqrt_square zl).
apply sqrt_le_1. 3: exact H1.
exact (Rle_0_sqr _).
exact H2.
exact (Rlt_le _ _ Hzl1).
rewrite <- (sqrt_square zu). 2: exact Hzu1.
apply sqrt_le_1.
exact H2.
exact (Rle_0_sqr _).
apply Rle_trans with (1 := Hyu) (2 := Hzu2).
split.
apply Rle_trans with (1 := Hzl1).
apply sqrt_positivity.
apply Rle_trans with (1 := Hzl2) (2 := Hyl).
rewrite <- (sqrt_square zu). 2: exact Hzu1.
apply sqrt_le_1.
apply Rle_trans with (1 := Hzl2) (2 := Hyl).
exact (Rle_0_sqr _).
apply Rle_trans with (1 := Hyu) (2 := Hzu2).
Qed.

Theorem IRcompose :
 forall xl xu yl yu zl zu : R,
 (-1 <= xl)%R -> (-1 <= yl)%R ->
 (zl <= xl + yl + xl * yl)%R -> (xu + yu + xu * yu <= zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x + y + x * y <= zu)%R.
intros xl xu yl yu zl zu Hx Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
replace (x + y + x * y)%R with ((1 + x) * (1 + y) - 1)%R. 2: ring.
assert (H : (1 + zl <= (1 + x) * (1 + y) <= 1 + zu)%R).
assert (H0 : (0 = 1 + -1)%R). ring.
assert (Hc : forall a b : R, ((1 + a) * (1 + b) = 1 + (a + b + a * b))%R).
intros a b. ring.
assert (Hi : forall a b c : R, (a <= b)%R -> (b <= c)%R -> (1 + a <= 1 + b <= 1 + c)%R).
intros a b c H1 H2. split.
apply Rplus_le_compat_l with (1 := H1).
apply Rplus_le_compat_l with (1 := H2).
apply IRmult_pp with (1 + xl)%R (1 + xu)%R (1 + yl)%R (1 + yu)%R.
rewrite H0. apply Rplus_le_compat_l with (1 := Hx).
rewrite H0. apply Rplus_le_compat_l with (1 := Hy).
rewrite Hc. apply Rplus_le_compat_l with (1 := Hzl).
rewrite Hc. apply Rplus_le_compat_l with (1 := Hzu).
apply Hi with (1 := Hxl) (2 := Hxu).
apply Hi with (1 := Hyl) (2 := Hyu).
assert (H0 : forall a : R, (a = (1 + a) + -1)%R).
intros a. ring.
split.
rewrite (H0 zl). exact (Rplus_le_compat_r _ _ _ (proj1 H)).
rewrite (H0 zu). exact (Rplus_le_compat_r _ _ _ (proj2 H)).
Qed.

Theorem IRcompose_inv :
 forall xl xu yl yu zl zu : R,
 (-1 <= xl)%R -> (-1 < yl)%R ->
 (yu + zl + yu * zl <= xl)%R -> (xu <= yl + zu + yl * zu)%R ->
 forall x y : R,
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= (x - y) / (1 + y) <= zu)%R.
intros xl xu yl yu zl zu Hx Hy Hzl Hzu x y (Hxl,Hxu) (Hyl,Hyu).
assert (H0: (0 = 1 + -1)%R). ring.
assert (Hc: (0 < 1 + yl)%R).
rewrite H0.
apply Rplus_lt_compat_l with (1 := Hy).
replace ((x - y) / (1 + y))%R with ((1 + x) / (1 + y) - 1)%R.
assert (H : (1 + zl <= (1 + x) / (1 + y) <= 1 + zu)%R).
assert (Hi : forall a b c : R, (a <= b)%R -> (b <= c)%R -> (1 + a <= 1 + b <= 1 + c)%R).
intros a b c H1 H2. split.
apply Rplus_le_compat_l with (1 := H1).
apply Rplus_le_compat_l with (1 := H2).
destruct (IRdiv_aux_p _ _ _ Hc (Hi _ _ _ Hyl Hyu))%R as (H1, (H2, (H3, (H4, H5)))).
unfold Rdiv.
apply IRmult_pp with (2 := H2) (5 := Hi _ _ _ Hxl Hxu) (6 := H5).
rewrite H0. apply Rplus_le_compat_l with (1 := Hx).
replace (1 + zl)%R with ((1 + zl) * (1 + yu) * /(1 + yu))%R.
apply monotony_2p with (1 := H2).
replace ((1 + zl) * (1 + yu))%R with (1 + (yu + zl + yu * zl))%R. 2: ring.
apply Rplus_le_compat_l with (1 := Hzl).
field. exact H4.
replace (1 + zu)%R with ((1 + zu) * (1 + yl) * /(1 + yl))%R.
apply monotony_2p with (1 := H1).
replace ((1 + zu) * (1 + yl))%R with (1 + (yl + zu + yl * zu))%R. 2: ring.
apply Rplus_le_compat_l with (1 := Hzu).
field. exact H3.
replace zl with (1 + zl + -1)%R. 2: ring.
replace zu with (1 + zu + -1)%R. 2: ring.
unfold Rminus.
split ; apply Rplus_le_compat_r.
exact (proj1 H).
exact (proj2 H).
field.
apply Rgt_not_eq.
unfold Rgt.
apply Rlt_le_trans with (1 := Hc).
apply Rplus_le_compat_l with (1 := Hyl).
Qed.

Theorem IRabs_p :
 forall yl yu zl zu : R,
 (0 <= yl)%R ->
 (zl <= yl)%R -> (yu <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= Rabs y <= zu)%R.
intros yl yu zl zu Hy Hzl Hzu y Hylu.
rewrite Rabs_pos_eq.
apply IRsubset with (1 := Hzl) (2 := Hzu) (3 := Hylu).
apply Rle_trans with (1 := Hy) (2 := proj1 Hylu).
Qed.

Theorem IRabs_o :
 forall yl yu zl zu : R,
 (zl <= 0)%R -> (-yl <= zu)%R -> (yu <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= Rabs y <= zu)%R.
intros yl yu zl zu Hzl Hzu1 Hzu2 y (Hyl,Hyu).
split.
apply Rle_trans with (1 := Hzl) (2 := Rabs_pos y).
unfold Rabs. case Rcase_abs ; intro H.
apply Rle_trans with (2 := Hzu1).
apply Ropp_le_contravar with (1 := Hyl).
apply Rle_trans with (1 := Hyu) (2 := Hzu2).
Qed.

Theorem IRabs_n :
 forall yl yu zl zu : R,
 (yu <= 0)%R ->
 (zl <= -yu)%R -> (-yl <= zu)%R ->
 forall y : R,
 (yl <= y <= yu)%R ->
 (zl <= Rabs y <= zu)%R.
intros yl yu zl zu Hy Hzl Hzu y Hylu.
rewrite Rabs_left1.
apply IRopp with (1 := Hzl) (2 := Hzu) (3 := Hylu).
apply Rle_trans with (1 := proj2 Hylu) (2 := Hy).
Qed.

End Gappa_real.
