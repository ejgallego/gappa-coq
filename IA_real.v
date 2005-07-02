Require Import Reals.

Section IA_real.

Record RR: Set := makepairR { lower : R ; upper : R }.

Definition IintR (xi : RR) (x : R) :=
 (lower xi <= x <= upper xi)%R.

Lemma IintR_abs :
 forall xi : RR, forall x : R,
 IintR xi x ->
 (Rabs x <= Rabs (lower xi))%R \/ (Rabs x <= Rabs (upper xi))%R.
intros xi x H.
case (Rle_or_lt 0 x); intro H0.
right.
repeat rewrite Rabs_right.
exact (proj2 H).
apply Rle_ge.
exact (Rle_trans _ _ _ H0 (proj2 H)).
exact (Rle_ge _ _ H0).
left.
repeat rewrite Rabs_left.
exact (Ropp_le_contravar _ _ (proj1 H)).
exact (Rle_lt_trans _ _ _ (proj1 H) H0).
exact H0.
Qed.

Definition IplusR_property (xi yi zi : RR) :=
 forall x y : R,
 IintR xi x -> IintR yi y -> IintR zi (x + y).

Theorem IplusR :
 forall xi yi zi : RR,
 (lower zi <= lower xi + lower yi)%R ->
 (upper xi + upper yi <= upper zi)%R ->
 IplusR_property xi yi zi.
intros xi yi zi Hl Hu x y Hx Hy.
unfold IintR in *.
split.
apply Rle_trans with (lower xi + lower yi)%R.
exact Hl.
apply Rplus_le_compat; intuition.
apply Rle_trans with (upper xi + upper yi)%R.
apply Rplus_le_compat; intuition.
exact Hu.
Qed.

Definition IplusR_fun (xi yi : RR) :=
 (makepairR (lower xi + lower yi)%R (upper xi + upper yi)%R).
 
Lemma IplusR_fun_correct :
 forall xi yi : RR,
 IplusR_property xi yi (IplusR_fun xi yi).
intros xi yi x y Ix Iy.
apply IplusR with xi yi; auto with real.
Qed.

Definition IoppR_fun (xi : RR) :=
 (makepairR (-upper xi)%R (-lower xi)%R).

Lemma IoppR_exact :
 forall xi : RR, forall x : R,
 IintR xi x -> IintR (IoppR_fun xi) (-x).
intros xi x H.
split.
exact (Ropp_le_contravar _ _ (proj2 H)).
exact (Ropp_le_contravar _ _ (proj1 H)).
Qed.

Lemma IoppR_exact_rev :
 forall xi : RR, forall x : R,
 IintR (IoppR_fun xi) (-x) -> IintR xi x.
unfold IintR.
simpl.
intros xi x (H1,H2).
auto with real.
Qed.

Definition IminusR_property (xi yi zi : RR) :=
 forall x y : R,
 IintR xi x -> IintR yi y -> IintR zi (x - y).

Theorem IminusR :
 forall xi yi zi : RR,
 (lower zi <= lower xi - upper yi)%R ->
 (upper xi - lower yi <= upper zi)%R ->
 IminusR_property xi yi zi.
intros xi yi zi Hl Hu x y Hx Hy.
unfold Rminus in *.
apply (IplusR _ (makepairR (-upper yi) (-lower yi)) _ Hl Hu _ (-y)%R Hx).
apply (IoppR_exact yi).
exact Hy.
Qed.

Definition IminusR_fun (xi yi : RR) :=
 (makepairR (lower xi - upper yi)%R (upper xi - lower yi)%R).
 
Lemma IminusR_fun_correct :
 forall xi yi : RR,
 IminusR_property xi yi (IminusR_fun xi yi).
intros xi yi x y Ix Iy.
apply IminusR with xi yi; auto with real.
Qed.

Lemma Rle_trans_and : forall a b c : R, (a <= b <= c)%R -> (a <= c)%R.
intros a b c H.
decompose [and] H.
apply Rle_trans with b; assumption.
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

Theorem ImultR_pp :
 forall xl xu yl yu zl zu x y : R,
 (0 <= xl)%R -> (0 <= yl)%R ->
 (zl <= xl * yl)%R -> (xu * yu <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hyl Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xl * yl)%R. exact Hzl.
apply Rle_trans with (xl * y)%R.
exact (monotony_1p _ _ _ Hxl (proj1 Hy)).
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hyl (proj1 Hy)) (proj1 Hx)).
apply Rle_trans with (xu * yu)%R. 2: exact Hzu.
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hxl (proj1 Hx)) (proj2 Hy)).
exact
 (monotony_2p _ _ _ (Rle_trans _ _ _ Hyl (Rle_trans_and _ _ _ Hy)) (proj2 Hx)).
Qed.

Theorem ImultR_po :
 forall xl xu yl yu zl zu x y : R,
 (0 <= xl)%R -> (yl <= 0)%R -> (0 <= yu)%R ->
 (zl <= xu * yl)%R -> (xu * yu <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hyl Hyu Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xu * yl)%R. exact Hzl.
apply Rle_trans with (x * yl)%R.
exact (monotony_2n _ _ _ Hyl (proj2 Hx)).
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hxl (proj1 Hx)) (proj1 Hy)).
apply Rle_trans with (xu * yu)%R. 2: exact Hzu.
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hxl (proj1 Hx)) (proj2 Hy)).
exact (monotony_2p _ _ _ Hyu (proj2 Hx)).
Qed.

Theorem ImultR_pn :
 forall xl xu yl yu zl zu x y : R,
 (0 <= xl)%R -> (yu <= 0)%R ->
 (zl <= xu * yl)%R -> (xl * yu <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hyu Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xu * yl)%R. exact Hzl.
apply Rle_trans with (xu * y)%R.
exact
 (monotony_1p _ _ _ (Rle_trans _ _ _ Hxl (Rle_trans_and _ _ _ Hx)) (proj1 Hy)).
exact (monotony_2n _ _ _ (Rle_trans _ _ _ (proj2 Hy) Hyu) (proj2 Hx)).
apply Rle_trans with (xl * yu)%R. 2: exact Hzu.
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ (Rle_trans _ _ _ Hxl (proj1 Hx)) (proj2 Hy)).
exact (monotony_2n _ _ _ Hyu (proj1 Hx)).
Qed.

Theorem ImultR_op :
 forall xl xu yl yu zl zu x y : R,
 (xl <= 0)%R ->
 (0 <= xu)%R ->
 (0 <= yl)%R ->
 (zl <= xl * yu)%R ->
 (xu * yu <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hxu Hyl Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xl * yu)%R. exact Hzl.
apply Rle_trans with (xl * y)%R.
exact (monotony_1n _ _ _ Hxl (proj2 Hy)).
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hyl (proj1 Hy)) (proj1 Hx)).
apply Rle_trans with (xu * yu)%R. 2: exact Hzu.
apply Rle_trans with (xu * y)%R.
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hyl (proj1 Hy)) (proj2 Hx)).
exact (monotony_1p _ _ _ Hxu (proj2 Hy)).
Qed.

Theorem ImultR_oo :
 forall xl xu yl yu zl zu x y : R,
 (xl <= 0)%R -> (0 <= xu)%R -> (yl <= 0)%R -> (0 <= yu)%R ->
 (zl <= xu * yl)%R -> (zl <= xl * yu)%R ->
 (xl * yl <= zu)%R -> (xu * yu <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hxu Hyl Hyu Hzl1 Hzl2 Hzu1 Hzu2 Hx Hy.
case (Rlt_le_dec 0 x); intro H.
generalize (Rlt_le _ _ H). clear H. intro H.
split.
apply Rle_trans with (xu * yl)%R. exact Hzl1.
apply Rle_trans with (x * yl)%R.
exact (monotony_2n _ _ _ Hyl (proj2 Hx)).
exact (monotony_1p _ _ _ H (proj1 Hy)).
apply Rle_trans with (xu * yu)%R. 2: exact Hzu2.
apply Rle_trans with (x * yu)%R.
exact (monotony_1p _ _ _ H (proj2 Hy)).
exact (monotony_2p _ _ _ Hyu (proj2 Hx)).
split.
apply Rle_trans with (xl * yu)%R. exact Hzl2.
apply Rle_trans with (x * yu)%R.
exact (monotony_2p _ _ _ Hyu (proj1 Hx)).
exact (monotony_1n _ _ _ H (proj2 Hy)).
apply Rle_trans with (xl * yl)%R. 2: exact Hzu1.
apply Rle_trans with (x * yl)%R.
exact (monotony_1n _ _ _ H (proj1 Hy)).
exact (monotony_2n _ _ _ Hyl (proj1 Hx)).
Qed.

Theorem ImultR_on :
 forall xl xu yl yu zl zu x y : R,
 (xl <= 0)%R -> (0 <= xu)%R -> (yu <= 0)%R ->
 (zl <= xu * yl)%R -> (xl * yl <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hxu Hyu Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xu * yl)%R. exact Hzl.
apply Rle_trans with (xu * y)%R.
exact (monotony_1p _ _ _ Hxu (proj1 Hy)).
exact (monotony_2n _ _ _ (Rle_trans _ _ _ (proj2 Hy) Hyu) (proj2 Hx)).
apply Rle_trans with (xl * yl)%R. 2: exact Hzu.
apply Rle_trans with (xl * y)%R.
exact (monotony_2n _ _ _ (Rle_trans _ _ _ (proj2 Hy) Hyu) (proj1 Hx)).
exact (monotony_1n _ _ _ Hxl (proj1 Hy)).
Qed.

Theorem ImultR_np :
 forall xl xu yl yu zl zu x y : R,
 (xu <= 0)%R -> (0 <= yl)%R ->
 (zl <= xl * yu)%R -> (xu * yl <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxu Hyl Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xl * yu)%R. exact Hzl.
apply Rle_trans with (x * yu)%R.
exact
 (monotony_2p _ _ _ (Rle_trans _ _ _ Hyl (Rle_trans_and _ _ _ Hy)) (proj1 Hx)).
exact (monotony_1n _ _ _ (Rle_trans _ _ _ (proj2 Hx) Hxu) (proj2 Hy)).
apply Rle_trans with (xu * yl)%R. 2: exact Hzu.
apply Rle_trans with (xu * y)%R.
exact (monotony_2p _ _ _ (Rle_trans _ _ _ Hyl (proj1 Hy)) (proj2 Hx)).
exact (monotony_1n _ _ _ Hxu (proj1 Hy)).
Qed.


Theorem ImultR_no :
 forall xl xu yl yu zl zu x y : R,
 (xu <= 0)%R -> (yl <= 0)%R -> (0 <= yu)%R ->
 (zl <= xl * yu)%R -> (xl * yl <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxu Hyl Hyu Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xl * yu)%R. exact Hzl.
apply Rle_trans with (x * yu)%R.
exact (monotony_2p _ _ _ Hyu (proj1 Hx)).
exact (monotony_1n _ _ _ (Rle_trans _ _ _ (proj2 Hx) Hxu) (proj2 Hy)).
apply Rle_trans with (xl * yl)%R. 2: exact Hzu.
apply Rle_trans with (x * yl)%R.
exact (monotony_1n _ _ _ (Rle_trans _ _ _ (proj2 Hx) Hxu) (proj1 Hy)).
exact (monotony_2n _ _ _ Hyl (proj1 Hx)).
Qed.

Theorem ImultR_nn :
 forall xl xu yl yu zl zu x y : R,
 (xu <= 0)%R -> (yu <= 0)%R ->
 (zl <= xu * yu)%R -> (xl * yl <= zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x * y <= zu)%R.
intros xl xu yl yu zl zu x y Hxu Hyu Hzl Hzu Hx Hy.
split.
apply Rle_trans with (xu * yu)%R. exact Hzl.
apply Rle_trans with (xu * y)%R.
exact (monotony_1n _ _ _ Hxu (proj2 Hy)).
exact (monotony_2n _ _ _ (Rle_trans _ _ _ (proj2 Hy) Hyu) (proj2 Hx)).
apply Rle_trans with (xl * yl)%R. 2: exact Hzu.
apply Rle_trans with (xl * y)%R.
exact (monotony_2n _ _ _ (Rle_trans _ _ _ (proj2 Hy) Hyu) (proj1 Hx)).
exact
 (monotony_1n _ _ _ (Rle_trans _ _ _ (Rle_trans_and _ _ _ Hx) Hxu) (proj1 Hy)).
Qed.

Inductive interval_sign (xi : RR) : Set :=
  | Nsign : (upper xi <= 0)%R -> interval_sign xi
  | Msign : (lower xi <= 0)%R -> (0 <= upper xi)%R -> interval_sign xi
  | Psign : (0 <= lower xi)%R -> interval_sign xi.

Lemma interval_sign_correct :
 forall xi : RR, (lower xi <= upper xi)%R -> interval_sign xi.
intros xi H.
case (Rlt_le_dec (upper xi) 0); intro H0.
exact (Nsign _ (Rlt_le _ _ H0)).
case (Rlt_le_dec (lower xi) 0); intro H1.
exact (Msign _ (Rlt_le _ _ H1) H0).
exact (Psign _ H1).
Qed.

Lemma IintR_sign :
 forall xi : RR, forall x : R,
 IintR xi x -> interval_sign xi.
intros xi x H.
apply interval_sign_correct.
unfold IintR in H. decompose [and] H.
apply Rle_trans with x; assumption.
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

Definition ImultR_property (xi yi zi : RR) :=
 forall x y : R,
 IintR xi x -> IintR yi y ->
 IintR zi (x * y).

Lemma ImultR :
 forall xi yi zi : RR,
 let xl := lower xi in let xu := upper xi in
 let yl := lower yi in let yu := upper yi in
 (lower zi <= Rmin (Rmin (xl * yl) (xl * yu)) (Rmin (xu * yl) (xu * yu)))%R ->
 (Rmax (Rmax (xl * yl) (xl * yu)) (Rmax (xu * yl) (xu * yu)) <= upper zi)%R ->
 ImultR_property xi yi zi.
intros xi yi zi xl xu yl yu Hzl Hzu x y Hx Hy.
decompose [and] (Rmin_trans _ _ _ Hzl).
decompose [and] (Rmin_trans _ _ _ H).
decompose [and] (Rmin_trans _ _ _ H0).
clear Hzl H H0.
decompose [and] (Rmax_trans _ _ _ Hzu).
decompose [and] (Rmax_trans _ _ _ H).
decompose [and] (Rmax_trans _ _ _ H0).
clear Hzu H H0.
unfold IintR.
case (IintR_sign _ _ Hx); case (IintR_sign _ _ Hy); intros.
apply ImultR_nn with xl xu yl yu; assumption.
apply ImultR_no with xl xu yl yu; assumption.
apply ImultR_np with xl xu yl yu; assumption.
apply ImultR_on with xl xu yl yu; assumption.
apply ImultR_oo with xl xu yl yu; assumption.
apply ImultR_op with xl xu yl yu; assumption.
apply ImultR_pn with xl xu yl yu; assumption.
apply ImultR_po with xl xu yl yu; assumption.
apply ImultR_pp with xl xu yl yu; assumption.
Qed.

Definition ImultR_fun (xi yi : RR) :=
 let xl := lower xi in let xu := upper xi in
 let yl := lower yi in let yu := upper yi in
 makepairR
 (Rmin (Rmin (xl * yl) (xl * yu)) (Rmin (xu * yl) (xu * yu)))%R
 (Rmax (Rmax (xl * yl) (xl * yu)) (Rmax (xu * yl) (xu * yu)))%R.

Lemma ImultR_fun_correct :
 forall xi yi : RR,
 ImultR_property xi yi (ImultR_fun xi yi).
intros xi yi x y Ix Iy.
apply ImultR with xi yi; auto with real.
Qed.

Lemma Rle_Rinv :
 forall x y : R, (0 < x)%R -> (x <= y)%R ->
 (/y <= /x)%R.
intros x y Hx Hy.
assert (0 < y)%R.
exact (Rlt_le_trans _ _ _ Hx Hy).
apply Rmult_le_reg_l with x. exact Hx.
apply Rmult_le_reg_l with y. exact H.
cutrewrite ((y * (x * /y) = x)%R).
cutrewrite ((y * (x * /x) = y)%R).
exact Hy.
field. apply Rlt_dichotomy_converse. right. exact Hx.
field. apply Rlt_dichotomy_converse. right. exact H.
Qed.

Lemma IinvR_p :
 forall yl yu zl zu y : R,
 (0 < yl)%R ->
 (yl <= y <= yu)%R ->
 (zl <= /yu)%R -> (/yl <= zu)%R ->
 (zl <= /y <= zu)%R.
intros yl yu zl zu y Hyl Hy Hzl Hzu.
split.
apply Rle_trans with (/yu)%R. exact Hzl.
apply Rle_Rinv.
exact (Rlt_le_trans _ _ _ Hyl (proj1 Hy)).
exact (proj2 Hy).
apply Rle_trans with (/yl)%R. 2: exact Hzu.
apply Rle_Rinv.
exact Hyl.
exact (proj1 Hy).
Qed.

Lemma IinvR_n :
 forall yl yu zl zu y : R,
 (yu < 0)%R ->
 (yl <= y <= yu)%R ->
 (zl <= /yu)%R -> (/yl <= zu)%R ->
 (zl <= /y <= zu)%R.
intros yl yu zl zu y Hyu Hy Hzl Hzu.
apply (IoppR_exact_rev (makepairR zl zu) (/y)).
rewrite Ropp_inv_permute.
unfold IintR. simpl.
apply IinvR_p with (-yu)%R (-yl)%R.
apply Ropp_0_gt_lt_contravar. exact Hyu.
apply (IoppR_exact (makepairR yl yu)).
exact Hy.
rewrite <- Ropp_inv_permute.
apply Ropp_le_contravar.
exact Hzu.
apply Rlt_dichotomy_converse. left.
exact (Rle_lt_trans _ _ _ (Rle_trans_and _ _ _ Hy) Hyu).
rewrite <- Ropp_inv_permute.
apply Ropp_le_contravar.
exact Hzl.
apply Rlt_dichotomy_converse. left. exact Hyu.
apply Rlt_dichotomy_converse. left.
exact (Rle_lt_trans _ _ _ (proj2 Hy) Hyu).
Qed.

Lemma IinvR :
 forall yi zi : RR, forall y : R,
 let yl := lower yi in let yu := upper yi in
 (yu < 0)%R \/ (0 < yl)%R ->
 IintR yi y ->
 (lower zi <= /yu)%R -> (/yl <= upper zi)%R ->
 IintR zi (/y).
intros yi zi y yl yu Hylu Hy Hzl Hzu.
decompose [or] Hylu.
exact (IinvR_n _ _ _ _ _ H Hy Hzl Hzu).
exact (IinvR_p _ _ _ _ _ H Hy Hzl Hzu).
Qed.

Definition IdivR_property (xi yi zi : RR) :=
 forall x y : R,
 IintR xi x -> IintR yi y ->
 IintR zi (x / y).

Lemma IdivR :
 forall xi yi zi : RR,
 let xl := lower xi in let xu := upper xi in
 let yl := lower yi in let yu := upper yi in
 (yu < 0)%R \/ (yl > 0)%R ->
 (lower zi <= Rmin (Rmin (xl / yu) (xl / yl)) (Rmin (xu / yu) (xu / yl)))%R ->
 (Rmax (Rmax (xl / yu) (xl / yl)) (Rmax (xu / yu) (xu / yl)) <= upper zi)%R ->
 IdivR_property xi yi zi.
intros xi yi zi xl xu yl yu Hylu Hzl Hzu x y Hx Hy.
unfold Rdiv in *.
apply (ImultR _ (makepairR (/yu) (/yl)) _ Hzl Hzu _ (/y)%R Hx).
apply (IinvR _ (makepairR (/yu) (/yl)) y Hylu).
exact Hy.
apply Req_le. trivial.
apply Req_le. trivial.
Qed.

Definition IdivR_fun (xi yi : RR) :=
 let xl := lower xi in let xu := upper xi in
 let yl := lower yi in let yu := upper yi in
 makepairR
 (Rmin (Rmin (xl / yu) (xl / yl)) (Rmin (xu / yu) (xu / yl)))%R
 (Rmax (Rmax (xl / yu) (xl / yl)) (Rmax (xu / yu) (xu / yl)))%R.

Lemma IdivR_fun_correct :
 forall xi yi : RR,
 (upper yi < 0)%R \/ (lower yi > 0)%R ->
 IdivR_property xi yi (IdivR_fun xi yi).
intros xi yi H x y Ix Iy.
apply IdivR with xi yi; auto with real.
Qed.

Lemma IdivR_aux_p :
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
exact (Rle_Rinv _ _ (Rlt_le_trans _ _ _ Hyl (proj1 Hy)) (proj2 Hy)).
exact (Rle_Rinv _ _ Hyl (proj1 Hy)).
Qed.

Theorem IdivR_pp :
 forall xl xu yl yu zl zu x y : R,
 (0 <= xl)%R ->
 (0 < yl)%R ->
 (yu * zl <= xl)%R ->
 (xu <= yl * zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hyl Hzl Hzu Hx Hy.
generalize (IdivR_aux_p _ _ _ Hyl Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply ImultR_pp with (1 := Hxl) (2 := Hy2) (5 := Hx) (6 := Hy5).
replace zl with (yu * zl * / yu)%R.
exact (monotony_2p _ _ _ Hy2 Hzl).
field. exact Hy4.
replace zu with (yl * zu * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzu).
field. exact Hy3.
Qed.

Theorem IdivR_op :
 forall xl xu yl yu zl zu x y : R,
 (xl <= 0)%R ->
 (0 <= xu)%R ->
 (0 < yl)%R ->
 (yl * zl <= xl)%R ->
 (xu <= yl * zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hxu Hyl Hzl Hzu Hx Hy.
generalize (IdivR_aux_p _ _ _ Hyl Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply ImultR_op with (1 := Hxl) (2 := Hxu) (3 := Hy2) (6 := Hx) (7 := Hy5).
replace zl with (yl * zl * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzl).
field. exact Hy3.
replace zu with (yl * zu * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzu).
field. exact Hy3.
Qed.

Theorem IdivR_np :
 forall xl xu yl yu zl zu x y : R,
 (xu <= 0)%R ->
 (0 < yl)%R ->
 (yl * zl <= xl)%R ->
 (xu <= yu * zu)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu x y Hxu Hyl Hzl Hzu Hx Hy.
generalize (IdivR_aux_p _ _ _ Hyl Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply ImultR_np with (1 := Hxu) (2 := Hy2) (5 := Hx) (6 := Hy5).
replace zl with (yl * zl * / yl)%R.
exact (monotony_2p _ _ _ Hy1 Hzl).
field. exact Hy3.
replace zu with (yu * zu * / yu)%R.
exact (monotony_2p _ _ _ Hy2 Hzu).
field. exact Hy4.
Qed.

Lemma Rle_Rinv_neg :
 forall x y : R,
 (y < 0)%R -> (x <= y)%R ->
 (/ y <= / x)%R.
intros x y Hy H.
pattern (/ x)%R ; rewrite <- Ropp_involutive.
pattern (/ y)%R ; rewrite <- Ropp_involutive.
apply Ropp_le_contravar.
repeat rewrite Ropp_inv_permute.
apply Rle_Rinv ; auto with real.
exact (Rlt_not_eq _ _ Hy).
exact (Rlt_not_eq _ _ (Rle_lt_trans _ _ _ H Hy)).
Qed.

Lemma IdivR_aux_n :
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

Theorem IdivR_pn :
 forall xl xu yl yu zl zu x y : R,
 (0 <= xl)%R ->
 (yu < 0)%R ->
 (xu <= yu * zl)%R ->
 (yl * zu <= xl)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hyu Hzl Hzu Hx Hy.
generalize (IdivR_aux_n _ _ _ Hyu Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply ImultR_pn with (1 := Hxl) (2 := Hy1) (5 := Hx) (6 := Hy5).
replace zl with (yu * zl * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzl).
field. exact Hy4.
replace zu with (yl * zu * / yl)%R.
exact (monotony_2n _ _ _ Hy1 Hzu).
field. exact Hy3.
Qed.

Theorem IdivR_on :
 forall xl xu yl yu zl zu x y : R,
 (xl <= 0)%R ->
 (0 <= xu)%R ->
 (yu < 0)%R ->
 (xu <= yu * zl)%R ->
 (yu * zu <= xl)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu x y Hxl Hxu Hyu Hzl Hzu Hx Hy.
generalize (IdivR_aux_n _ _ _ Hyu Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply ImultR_on with (1 := Hxl) (2 := Hxu) (3 := Hy1) (6 := Hx) (7 := Hy5).
replace zl with (yu * zl * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzl).
field. exact Hy4.
replace zu with (yu * zu * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzu).
field. exact Hy4.
Qed.

Theorem IdivR_nn :
 forall xl xu yl yu zl zu x y : R,
 (xu <= 0)%R ->
 (yu < 0)%R ->
 (xu <= yl * zl)%R ->
 (yu * zu <= xl)%R ->
 (xl <= x <= xu)%R -> (yl <= y <= yu)%R ->
 (zl <= x / y <= zu)%R.
intros xl xu yl yu zl zu x y Hxu Hyu Hzl Hzu Hx Hy.
generalize (IdivR_aux_n _ _ _ Hyu Hy).
intros (Hy1, (Hy2, (Hy3, (Hy4, Hy5)))).
unfold Rdiv.
apply ImultR_nn with (1 := Hxu) (2 := Hy1) (5 := Hx) (6 := Hy5).
replace zl with (yl * zl * / yl)%R.
exact (monotony_2n _ _ _ Hy1 Hzl).
field. exact Hy3.
replace zu with (yu * zu * / yu)%R.
exact (monotony_2n _ _ _ Hy2 Hzu).
field. exact Hy4.
Qed.

End IA_real.
