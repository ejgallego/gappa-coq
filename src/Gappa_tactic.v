Require Import Reals.
Require Import List.
Require Import Fcore.
Require Export Gappa_library.

Strategy 1000 [Fcore_generic_fmt.round].

Module Gappa_Private.

(* factor an integer into odd*2^e *)
Definition float2_of_pos x :=
  let fix aux (m : positive) e { struct m } :=
    match m with
    | xO p => aux p (Zsucc e)
    | _ => Float2 (Zpos m) e
    end in
  aux x Z0.

Lemma float2_of_pos_correct :
  forall x, float2R (float2_of_pos x) = Z2R (Zpos x).
Proof.
intros x.
unfold float2_of_pos.
rewrite <- (Rmult_1_r (Z2R (Zpos x))).
change (Z2R (Zpos x) * 1)%R with (float2R (Float2 (Zpos x) 0%Z)).
generalize 0%Z.
induction x ; intros e ; try apply refl_equal.
rewrite IHx.
unfold float2R.
simpl.
replace (Zpos (xO x)) with (Zpos x * 2)%Z.
exact (Gappa_round_aux.float2_shift_p1 _ _).
now rewrite Zmult_comm.
Qed.

Definition compact_float2 m e :=
  match m with
  | Z0 => Float2 0 0
  | Zpos p =>
    match float2_of_pos p with
    | Float2 m e1 => Float2 m (e + e1)
    end
  | Zneg p =>
    match float2_of_pos p with
    | Float2 m e1 => Float2 (-m) (e + e1)
    end
  end.

Lemma compact_float2_correct :
  forall m e, float2R (compact_float2 m e) = float2R (Float2 m e).
Proof.
unfold float2R, F2R. simpl.
intros [|m|m] e ; simpl.
now rewrite 2!Rmult_0_l.
change (P2R m) with (Z2R (Zpos m)).
rewrite <- (float2_of_pos_correct m).
destruct (float2_of_pos m) as (m1, e1).
simpl.
rewrite Zplus_comm.
now rewrite bpow_plus, <- Rmult_assoc.
change (- P2R m)%R with (- (Z2R (Zpos m)))%R.
rewrite <- (float2_of_pos_correct m).
destruct (float2_of_pos m) as (m1, e1).
simpl.
rewrite Zplus_comm.
rewrite bpow_plus, <- Rmult_assoc.
now rewrite Z2R_opp, Ropp_mult_distr_l_reverse.
Qed.

Inductive UnaryOp : Set :=
  | uoNeg | uoSqrt | uoAbs | uoInv.

Inductive BinaryOp : Set :=
  | boAdd | boSub | boMul | boDiv.

Inductive Format : Set :=
  | fFixed : Z -> Format
  | fFloat : Z -> Z -> Format.

Inductive Mode : Set :=
  | mRndDN
  | mRndUP
  | mRndZR
  | mRndNE
  | mRndNA.

(* represent an expression on real numbers *)
Inductive RExpr :=
  | reUnknown : positive -> RExpr
  | reInteger : Z -> RExpr
  | reFloat2 : Z -> Z -> RExpr
  | reFloat10 : Z -> Z -> RExpr
  | reUnary : UnaryOp -> RExpr -> RExpr
  | reBinary : BinaryOp -> RExpr -> RExpr -> RExpr
  | reBpow2 : Z -> RExpr
  | reBpow10 : Z -> RExpr
  | rePow2 : Z -> RExpr
  | rePow10 : Z -> RExpr
  | reINR : positive -> RExpr
  | reIZR : Z -> RExpr
  | reRound : Format -> Mode -> RExpr -> RExpr.

Scheme Equality for positive.
Scheme Equality for Z.
Scheme Equality for UnaryOp.
Scheme Equality for BinaryOp.
Scheme Equality for Format.
Scheme Equality for Mode.
Scheme Equality for RExpr.

(* represent an atomic proposition *)
Inductive RAtom :=
  | raBound : option RExpr -> RExpr -> option RExpr -> RAtom
  | raRel : RExpr -> RExpr -> RExpr -> RExpr -> RAtom
  | raLe : RExpr -> RExpr -> RAtom
  | raEq : RExpr -> RExpr -> RAtom
  | raFormat : Format -> RExpr -> RAtom.

Inductive RTree :=
  | rtTrue : RTree
  | rtFalse : RTree
  | rtAtom : RAtom -> RTree
  | rtNot : RTree -> RTree
  | rtAnd : RTree -> RTree -> RTree
  | rtOr : RTree -> RTree -> RTree
  | rtImpl : RTree -> RTree -> RTree.

Section Convert.

Definition convert_format (f : Format) : Z -> Z :=
  match f with
  | fFloat e p => FLT_exp e p
  | fFixed e => FIX_exp e
  end.

Definition convert_mode (m : Mode) : R -> Z :=
  match m with
  | mRndZR => Ztrunc
  | mRndDN => Zfloor
  | mRndUP => Zceil
  | mRndNE => rndNE
  | mRndNA => rndNA
  end.

Variable unknown_values : list R.

(* convert to an expression on real numbers *)
Fixpoint convert_expr (t : RExpr) : R :=
  match t with
  | reUnknown x =>
    nth (nat_of_P x) (R0 :: unknown_values) R0
  | reInteger x => Z2R x
  | reFloat2 x y => float2R (Float2 x y)
  | reFloat10 x y => float10R (Float10 x y)
  | reUnary o x =>
    match o with
    | uoNeg  => Ropp
    | uoSqrt => sqrt
    | uoAbs  => Rabs
    | uoInv  => Rinv
    end (convert_expr x)
  | reBinary o x y =>
    match o with
    | boAdd => Rplus
    | boSub => Rminus
    | boMul => Rmult
    | boDiv => Rdiv
    end (convert_expr x) (convert_expr y)
  | reBpow2 x =>
    bpow radix2 x
  | reBpow10 x =>
    bpow radix10 x
  | rePow2 x =>
    powerRZ 2%R x
  | rePow10 x =>
    powerRZ 10%R x
  | reINR x =>
    INR (nat_of_P x)
  | reIZR x =>
    IZR x
  | reRound f m x =>
    Fcore_generic_fmt.round radix2 (convert_format f) (convert_mode m) (convert_expr x)
  end.

(* convert to an atomic proposition *)
Definition convert_atom (a : RAtom) : Prop :=
  match a with
  | raBound None _ None => True
  | raBound (Some l) e None => (convert_expr l <= convert_expr e)%R
  | raBound None e (Some u) => (convert_expr e <= convert_expr u)%R
  | raBound (Some l) e (Some u) => (convert_expr l <= convert_expr e <= convert_expr u)%R
  | raRel er ex l u => exists eps : R, (convert_expr l <= eps <= convert_expr u)%R /\ (convert_expr er = convert_expr ex * (1 + eps))%R
  | raLe x y => (convert_expr x <= convert_expr y)%R
  | raEq x y => (convert_expr x = convert_expr y)%R
  | raFormat f x => generic_format radix2 (convert_format f) (convert_expr x)
  end.

Fixpoint convert_tree (t : RTree) : Prop :=
  match t with
  | rtTrue => True
  | rtFalse => False
  | rtAtom a => convert_atom a
  | rtNot t => not (convert_tree t)
  | rtAnd t1 t2 => (convert_tree t1) /\ (convert_tree t2)
  | rtOr t1 t2 => (convert_tree t1) \/ (convert_tree t2)
  | rtImpl t1 t2 => (convert_tree t1) -> (convert_tree t2)
  end.

Lemma decidable_atom :
  forall a, { convert_atom a } + { not (convert_atom a) }.
Proof.
intros [[l|] e [u|]|x y l u|x y|x y|fmt x] ; simpl.
destruct (Rle_lt_dec (convert_expr l) (convert_expr e)) as [Hl|Hl].
destruct (Rle_lt_dec (convert_expr e) (convert_expr u)) as [Hu|Hu].
now left ; split.
right.
intros (_,H).
now apply Rlt_not_le with (1 := Hu).
right.
intros (H,_).
now apply Rlt_not_le with (1 := Hl).
destruct (Rle_lt_dec (convert_expr l) (convert_expr e)) as [Hl|Hl].
now left.
right.
now apply Rlt_not_le.
destruct (Rle_lt_dec (convert_expr e) (convert_expr u)) as [Hu|Hu].
now left.
right.
now apply Rlt_not_le.
now left.
destruct (Req_EM_T (convert_expr y) 0) as [Zy|Zy].
destruct (Req_EM_T (convert_expr x) 0) as [Zx|Zx].
destruct (Rle_lt_dec (convert_expr l) (convert_expr u)) as [H|H].
left.
exists (convert_expr l).
split.
split.
apply Rle_refl.
exact H.
now rewrite Zy, Rmult_0_l.
right.
intros (eps,((H1,H2),_)).
apply Rlt_not_le with (1 := H).
now apply Rle_trans with eps.
right.
intros (eps,(_,H')).
now rewrite Zy, Rmult_0_l in H'.
destruct (Rle_lt_dec (convert_expr l) (convert_expr x / convert_expr y - 1)) as [Hl|Hl].
destruct (Rle_lt_dec (convert_expr x / convert_expr y - 1) (convert_expr u)) as [Hu|Hu].
left.
exists (convert_expr x / convert_expr y - 1)%R.
split.
now split.
now field.
right.
intros (eps,((_,H),H')).
apply Rlt_not_le with (1 := Hu).
rewrite H'.
now replace (convert_expr y * (1 + eps) / convert_expr y - 1)%R with eps ; [idtac | field].
right.
intros (eps,((H,_),H')).
apply Rlt_not_le with (1 := Hl).
rewrite H'.
now replace (convert_expr y * (1 + eps) / convert_expr y - 1)%R with eps ; [idtac | field].
destruct (Rle_lt_dec (convert_expr x) (convert_expr y)) as [H|H].
now left.
right.
now apply Rlt_not_le.
apply Req_EM_T.
apply Req_EM_T.
Qed.

Lemma decidable_tree :
  forall t, { convert_tree t } + { not (convert_tree t) }.
Proof.
induction t as [| |a|t Ht|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2].
now left.
now right.
apply decidable_atom.
destruct Ht as [Ht|Ht].
now right.
now left.
destruct Ht1 as [Ht1|Ht1].
destruct Ht2 as [Ht2|Ht2].
now left ; split.
right.
now intros (_,H).
right.
now intros (H,_).
destruct Ht1 as [Ht1|Ht1].
left.
now left.
destruct Ht2 as [Ht2|Ht2].
left.
now right.
right.
now intros [H|H].
destruct Ht2 as [Ht2|Ht2].
left.
now intros _.
destruct Ht1 as [Ht1|Ht1].
right.
contradict Ht2.
now apply Ht2.
left.
now intros H.
Qed.

Fixpoint normalize_tree (t : RTree) (pos : bool) :=
  match t with
  | rtTrue => if pos then rtTrue else rtFalse
  | rtFalse => if pos then rtFalse else rtTrue
  | rtAtom a => if pos then t else rtNot t
  | rtNot t => normalize_tree t (negb pos)
  | rtImpl t1 t2 => (if pos then rtOr else rtAnd) (normalize_tree t1 (negb pos)) (normalize_tree t2 pos)
  | rtOr t1 t2 => (if pos then rtOr else rtAnd) (normalize_tree t1 pos) (normalize_tree t2 pos)
  | rtAnd t1 t2 => (if pos then rtAnd else rtOr) (normalize_tree t1 pos) (normalize_tree t2 pos)
  end.

Theorem normalize_tree_correct :
  forall t pos,
  convert_tree (normalize_tree t pos) <-> if pos then convert_tree t else not (convert_tree t).
Proof.
induction t as [| |a|t Ht|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2] ;
  destruct pos ; split ; simpl ; try easy.
intros H.
now apply H.
apply (Ht false).
apply (Ht false).
intros H.
intros H'.
apply H'.
now apply (Ht true).
intros H.
apply (Ht true).
now destruct (decidable_tree t) as [H'|H'].
intros (H1,H2).
split.
now apply (Ht1 true).
now apply (Ht2 true).
intros (H1,H2).
split.
now apply (Ht1 true).
now apply (Ht2 true).
intros [H|H] (H1,H2).
now apply (Ht1 false).
now apply (Ht2 false).
specialize (Ht1 false).
specialize (Ht2 false).
intros H.
destruct (decidable_tree t1) as [H'|H'].
right.
apply Ht2.
contradict H.
now split.
left.
now apply Ht1.
intros [H|H].
left.
now apply (Ht1 true).
right.
now apply (Ht2 true).
intros [H|H].
left.
now apply (Ht1 true).
right.
now apply (Ht2 true).
intros (H1,H2) [H|H].
now apply (Ht1 false).
now apply (Ht2 false).
intros H.
split.
apply (Ht1 false).
contradict H.
now left.
apply (Ht2 false).
contradict H.
now right.
intros [H|H] H'.
now apply (Ht1 false) in H.
now apply (Ht2 true).
intros H.
destruct (decidable_tree t1) as [H'|H'].
right.
apply (Ht2 true).
now apply H.
left.
now apply (Ht1 false).
intros (H1,H2) H'.
apply (Ht1 true) in H1.
apply H' in H1.
now apply (Ht2 false).
intros H.
split.
destruct (decidable_tree t1) as [H'|H'].
now apply (Ht1 true).
now elim H.
apply (Ht2 false).
now contradict H.
Qed.

Fixpoint simplify_tree (t : RTree) :=
  match t with
  | rtNot rtTrue => rtFalse
  | rtNot rtFalse => rtTrue
  | rtAnd t1 t2 =>
    match simplify_tree t1, simplify_tree t2 with
    | rtTrue, t => t
    | rtFalse, _ => rtFalse
    | t, rtTrue => t
    | _, rtFalse => rtFalse
    | t1, t2 => rtAnd t1 t2
    end
  | rtOr t1 t2 =>
    match simplify_tree t1, simplify_tree t2 with
    | rtTrue, _ => rtTrue
    | rtFalse, t => t
    | _, rtTrue => rtTrue
    | t, rtFalse => t
    | t1, t2 => rtOr t1 t2
    end
  | _ => t
  end.

Theorem simplify_tree_correct :
  forall t,
  convert_tree t -> convert_tree (simplify_tree t).
Proof.
induction t as [| |a|t Ht|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2] ; try easy.
destruct t ; try easy.
intros H.
now apply H.
intros (H1,H2).
specialize (Ht1 H1).
specialize (Ht2 H2).
simpl.
destruct (simplify_tree t1) ; try easy ; destruct (simplify_tree t2) ; try easy ; split ; easy.
intros [H|H].
specialize (Ht1 H).
simpl.
destruct (simplify_tree t1) ; try easy ; destruct (simplify_tree t2) ; try easy ; left ; easy.
specialize (Ht2 H).
simpl.
destruct (simplify_tree t1) ; try easy ; destruct (simplify_tree t2) ; try easy ; right ; easy.
Qed.

Section StableExpr.

Definition stable_expr f :=
  forall t, convert_expr (f t) = convert_expr t.

Variable chg_expr : RExpr -> RExpr.

(* apply a function recursively, starting from the leafs of an expression *)
Fixpoint transform_expr (t : RExpr) :=
  chg_expr
    match t with
    | reUnary o x => reUnary o (transform_expr x)
    | reBinary o x y => reBinary o (transform_expr x) (transform_expr y)
    | reRound f m x => reRound f m (transform_expr x)
    | _ => t
    end.

Theorem transform_expr_correct :
  stable_expr chg_expr ->
  stable_expr transform_expr.
Proof.
unfold stable_expr.
intros Hf t.
induction t ; simpl ; rewrite Hf ; simpl ; try easy.
now rewrite IHt.
now rewrite IHt1, IHt2.
now rewrite IHt.
Qed.

End StableExpr.

Definition stable_atom f :=
  forall a, convert_atom (f a) <-> convert_atom a.

Definition transform_atom_bound f a :=
  match a with
  | raBound (Some l) e (Some u) => raBound (Some (f l)) e (Some (f u))
  | raBound (Some l) e None => raBound (Some (f l)) e None
  | raBound None e (Some u) => raBound None e (Some (f u))
  | raRel er ex l u => raRel er ex (f l) (f u)
  | _ => a
  end.

Theorem transform_atom_bound_correct :
  forall f,
  stable_expr f ->
  stable_atom (transform_atom_bound (transform_expr f)).
Proof.
now intros f Hf [[l|] e [u|]|x y l u|x y|x y|fmt x] ;
  simpl ; split ; repeat rewrite (transform_expr_correct _ Hf).
Qed.

Definition transform_atom_expr f a :=
  match a with
  | raBound l e u => raBound l (f e) u
  | raRel er ex l u => raRel (f er) (f ex) l u
  | raEq ex ey => raEq (f ex) (f ey)
  | raLe ex ey => raLe (f ex) (f ey)
  | raFormat fmt e => raFormat fmt (f e)
  end.

Theorem transform_atom_expr_correct :
  forall f,
  stable_expr f ->
  stable_atom (transform_atom_expr (transform_expr f)).
Proof.
now intros f Hf [l e u|x y l u|x y|x y|fmt x] ;
  simpl ; split ; repeat rewrite (transform_expr_correct _ Hf).
Qed.

Definition stable_tree f :=
  forall t, convert_tree (f t) <-> convert_tree t.

Section StableTree.

Variable chg_atom : RAtom -> RAtom.

Fixpoint transform_tree_atom (t : RTree) : RTree :=
  match t with
  | rtTrue => rtTrue
  | rtFalse => rtFalse
  | rtAtom a => rtAtom (chg_atom a)
  | rtNot t => rtNot (transform_tree_atom t)
  | rtAnd t1 t2 => rtAnd (transform_tree_atom t1) (transform_tree_atom t2)
  | rtOr t1 t2 => rtOr (transform_tree_atom t1) (transform_tree_atom t2)
  | rtImpl t1 t2 => rtImpl (transform_tree_atom t1) (transform_tree_atom t2)
  end.

Theorem transform_tree_atom_correct :
  stable_atom chg_atom ->
  stable_tree transform_tree_atom.
Proof.
intros Hs t.
induction t as [| |a|t Ht|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2] ; simpl ; intuition.
now apply Hs.
now apply Hs.
Qed.

End StableTree.

Definition stable_atom_tree f :=
  forall a (pos : bool),
  (if pos then convert_atom a else not (convert_atom a)) ->
  convert_tree (f pos a).

Section StableTree'.

Variable chg_atom : bool -> RAtom -> RTree.

Fixpoint transform_tree_atom' (t : RTree) : RTree :=
  match t with
  | rtTrue => rtTrue
  | rtFalse => rtFalse
  | rtAtom a => chg_atom true a
  | rtNot (rtAtom a) => chg_atom false a
  | rtAnd t1 t2 => rtAnd (transform_tree_atom' t1) (transform_tree_atom' t2)
  | rtOr t1 t2 => rtOr (transform_tree_atom' t1) (transform_tree_atom' t2)
  | _ => t
  end.

Theorem transform_tree_atom'_correct :
  stable_atom_tree chg_atom ->
  forall t,
  convert_tree t -> convert_tree (transform_tree_atom' t).
Proof.
intros Hs t.
induction t as [| |a|t Ht|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2|t1 Ht1 t2 Ht2] ; simpl ; intuition.
destruct t ; intuition.
Qed.

End StableTree'.

(* transform INR and IZR into real integers, change a/b and a*2^b into floats *)
Definition gen_float_func t :=
  match t with
  | reUnary uoNeg (reInteger (Zpos x)) =>
    reInteger (Zneg x)
  | reBinary boDiv (reInteger x) (reInteger (Zpos y)) =>
    match float2_of_pos y with
    | Float2 1 (Zpos y') => reFloat2 x (Zneg y')
    | _ => t
    end
  | reBinary boMul (reInteger x) (reBpow2 y) =>
    reFloat2 x y
  | reBinary boMul (reInteger x) (reBpow10 y) =>
    reFloat10 x y
  | reBinary boMul (reInteger x) (rePow2 y) =>
    reFloat2 x y
  | reBinary boMul (reInteger x) (rePow10 y) =>
    reFloat10 x y
  | reINR x =>
    reInteger (Zpos x)
  | reIZR x =>
    reInteger x
  | _ => t
  end.

Lemma gen_float_prop :
  stable_expr gen_float_func.
Proof.
intros [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try apply refl_equal.
(* unary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
destruct z ; apply refl_equal.
(* binary ops *)
destruct o ; try apply refl_equal ;
  destruct x ; try apply refl_equal ;
  destruct y ; try apply refl_equal.
(* . x * 2^y *)
simpl.
now rewrite <- (bpow_powerRZ radix2).
(* . x * 10^y *)
simpl.
now rewrite <- (bpow_powerRZ radix10).
(* . x / 2*2*2*2 *)
destruct z0 ; try apply refl_equal.
generalize (float2_of_pos_correct p).
simpl.
destruct (float2_of_pos p) as ([|[m|m|]|m], [|e|e]) ; intros H ; try apply refl_equal.
rewrite <- H.
unfold convert_expr.
unfold float2R, F2R at 2. simpl.
now rewrite Rmult_1_l.
(* INR *)
exact (P2R_INR _).
(* IZR *)
exact (Z2R_IZR _).
Qed.

(* remove pending powerRZ *)
Definition clean_pow_func t :=
  match t with
  | reBpow2 x => reFloat2 1 x
  | reBpow10 x => reFloat10 1 x
  | rePow2 x => reFloat2 1 x
  | rePow10 x => reFloat10 1 x
  | _ => t
  end.

Lemma clean_pow_prop :
  stable_expr clean_pow_func.
Proof.
intros [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try apply refl_equal.
apply (F2R_bpow radix2 x).
apply (F2R_bpow radix10 x).
simpl.
unfold float2R.
rewrite F2R_bpow.
apply bpow_powerRZ.
simpl.
unfold float10R.
rewrite F2R_bpow.
apply bpow_powerRZ.
Qed.

(* compute on constant terms, so that they are hopefully represented by a single float *)
Definition merge_float2_aux m e :=
  match compact_float2 m e with
  | Float2 m1 e1 => reFloat2 m1 e1
  end.

Definition merge_float2_func t :=
  match t with
  | reInteger x => merge_float2_aux x 0
  | reUnary uoNeg (reFloat2 x y) => merge_float2_aux (- x) y
  | reBinary boMul (reFloat2 x1 y1) (reFloat2 x2 y2) => merge_float2_aux (x1 * x2) (y1 + y2)
  | reFloat2 x y => merge_float2_aux x y
  | _ => t
  end.

Lemma merge_float2_prop :
  stable_expr merge_float2_func.
Proof.
assert (forall m e, convert_expr (merge_float2_aux m e) = convert_expr (reFloat2 m e)).
intros.
unfold merge_float2_aux.
generalize (compact_float2_correct m e).
now destruct (compact_float2 m e).
(* . *)
intros [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try apply refl_equal ; try exact (H x _).
(* integer *)
simpl.
unfold merge_float2_aux.
generalize (compact_float2_correct x 0).
rewrite <- (Rmult_1_r (Z2R x)).
now destruct (compact_float2 x 0).
(* unary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
simpl.
rewrite H.
now rewrite <- Gappa_dyadic.Fopp2_correct.
(* binary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
destruct y ; try apply refl_equal.
simpl.
rewrite H.
now rewrite <- Gappa_dyadic.Fmult2_correct.
Qed.

(* change /a into 1/a *)
Definition remove_inv_func t :=
  match t with
  | reUnary uoInv x => reBinary boDiv (reInteger 1) x
  | _ => t
  end.

Lemma remove_inv_prop :
  stable_expr remove_inv_func.
Proof.
intros [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try apply refl_equal.
destruct o ; try apply refl_equal.
exact (Rmult_1_l _).
Qed.

Definition get_float2_bound b := transform_expr merge_float2_func (transform_expr clean_pow_func
  (transform_expr gen_float_func (transform_expr remove_inv_func b))).

Lemma get_float2_bound_correct :
  stable_expr get_float2_bound.
Proof.
intros b.
unfold get_float2_bound.
rewrite (transform_expr_correct _ merge_float2_prop).
rewrite (transform_expr_correct _ clean_pow_prop).
rewrite (transform_expr_correct _ gen_float_prop).
now rewrite (transform_expr_correct _ remove_inv_prop).
Qed.

Definition change_abs_func a :=
  match a with
  | raLe (reUnary uoAbs u as u') v => raBound (Some (reFloat2 0 0)) u' (Some v)
  | _ => a
  end.

Lemma change_abs_prop :
  stable_atom change_abs_func.
Proof.
intros [l v u|x y l u|v w|v w|f x] ; try easy.
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try easy.
destruct o ; try easy.
split.
now intros (_,H).
split.
replace (convert_expr (reFloat2 0 0)) with R0.
apply Rabs_pos.
apply eq_sym, Rmult_0_l.
exact H.
Qed.

Lemma change_rel_aux:
  forall x y b, (0 <= b /\ Rabs (x - y) <= b * Rabs y)%R <-> (exists eps, -b <= eps <= b /\ x = y * (1 + eps))%R.
Proof.
intros x y b.
split.
(* . *)
intros (H1, H2).
destruct (Req_dec y 0) as [Hy|Hy].
exists R0.
repeat split.
rewrite <- Ropp_0.
now apply Ropp_le_contravar.
apply H1.
rewrite Hy, Rmult_0_l.
destruct (Req_dec x 0) as [Hx|Hx] ; try exact Hx.
elim Rabs_no_R0 with (1 := Hx).
apply Rle_antisym.
now rewrite Hy, Rminus_0_r, Rabs_R0, Rmult_0_r in H2.
apply Rabs_pos.
exists ((x - y) / y)%R.
split.
2: now field.
apply Rabs_def2b.
apply Rmult_le_reg_l with (Rabs y).
now apply Rabs_pos_lt.
rewrite <- Rabs_mult.
replace (y * ((x - y) / y))%R with (x - y)%R by now field.
now rewrite Rmult_comm.
(* . *)
intros (eps, (H1, H2)).
repeat split.
destruct (Rle_or_lt 0 b) as [H|H] ; try exact H.
apply Ropp_le_cancel.
apply Rle_trans with b.
now apply Rle_trans with eps.
apply Rlt_le.
now rewrite Ropp_0.
rewrite H2.
replace (y * (1 + eps) - y)%R with (eps * y)%R by ring.
rewrite Rabs_mult.
apply Rmult_le_compat_r.
apply Rabs_pos.
unfold Rabs.
destruct (Rcase_abs eps) as [H|H].
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
apply H1.
Qed.

Definition change_rel_func a :=
  match a with
  | raLe (reUnary uoAbs (reBinary boSub er ex)) (reBinary boMul u (reUnary uoAbs ex')) =>
    if RExpr_beq ex ex' then
      match get_float2_bound u with
      | reFloat2 (Zpos m) e => raRel er ex (reFloat2 (Zneg m) e) (reFloat2 (Zpos m) e)
      | _ => a
      end
    else a
  | _ => a
  end.

Lemma change_rel_prop :
  stable_atom change_rel_func.
Proof.
unfold change_rel_func.
intros [l v u|x y l u|v w|v w|f x] ; try easy.
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try easy.
destruct o ; try easy.
destruct x as [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ; try easy.
destruct o ; try easy.
destruct w as [u|u|u v|u v|o u|o u v|u|u|u|u|u|u|f m u] ; try easy.
destruct o ; try easy.
destruct v as [v|v|v w|v w|o v|o v w|v|v|v|v|v|v|f m v] ; try easy.
destruct o ; try easy.
case_eq (RExpr_beq y v) ; try easy.
intros Hb.
rewrite <- internal_RExpr_dec_bl with (1 := Hb).
assert (H := get_float2_bound_correct u).
destruct (get_float2_bound u) as [u1|u1|m e|u1 u2|o u1|o u1 u2|u1|u1|u1|u1|u1|u1|f u1] ; try easy.
destruct m as [|m|m] ; try easy.
simpl in H |- *.
change (Float2 (Zneg m) e) with (Gappa_dyadic.Fopp2 (Float2 (Zpos m) e)).
rewrite Gappa_dyadic.Fopp2_correct.
rewrite H.
split ; intro H'.
now apply <- change_rel_aux.
apply -> change_rel_aux.
split.
rewrite <- H.
now apply (Gappa_dyadic.Fpos0_correct (Float2 (Zpos m) e)).
exact H'.
Qed.

Definition change_format_func (pos : bool) a :=
  let a' :=
    match a with
    | raFormat (fFixed _ as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | raFormat (fFloat _ (Zpos _) as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | _ => a
    end in
  if pos then rtAtom a' else rtNot (rtAtom a').

Lemma change_format_prop :
  stable_atom_tree change_format_func.
Proof.
unfold change_format_func.
intros [l v u|x y l u|v w|v w|[em|em [|p|p]] x] pos ; try (case pos ; easy) ; simpl ; intros H.
destruct pos ; simpl.
apply sym_eq, round_generic.
apply valid_rnd_N.
exact H.
contradict H.
rewrite <- H.
apply generic_format_round.
apply FIX_exp_valid.
apply valid_rnd_N.
destruct pos ; simpl.
apply sym_eq, round_generic.
apply valid_rnd_N.
exact H.
contradict H.
rewrite <- H.
apply generic_format_round.
now apply FLT_exp_valid.
apply valid_rnd_N.
Qed.

Definition remove_unknown_func (pos : bool) a :=
  match a with
  | raBound (Some l) _ (Some u) =>
    match l with
    | reInteger _
    | reFloat2 _ _ =>
      match u with
      | reInteger _
      | reFloat2 _ _ => if pos then rtAtom a else rtNot (rtAtom a)
      | _ => rtTrue
      end
    | _ => rtTrue
    end
  | raRel _ _ (reFloat2 _ _) (reFloat2 _ _) => if pos then rtAtom a else rtNot (rtAtom a)
  | raEq _ _ => if pos then rtAtom a else rtNot (rtAtom a)
  | _ => rtTrue
  end.

Lemma remove_unknown_prop :
  stable_atom_tree remove_unknown_func.
Proof.
intros [[l|] v [u|]|x y l u|v w|v w|[em|em [|p|p]] x] pos ; try (case pos ; easy) ; simpl ; intros H.
destruct l as [xl|xl|xl yl|xl yl|ol xl|ol xl yl|xl|xl|xl|xl|xl|xl|fl xl] ; try easy.
destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|xu|xu|xu|fu xu] ; try easy.
now destruct pos.
now destruct pos.
destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|xu|xu|xu|fu xu] ; try easy.
now destruct pos.
now destruct pos.
destruct l as [l|l|l l'|l l'|o l|o l l'|l|l|l|l|l|l|f l] ; try easy.
destruct u as [u|u|u u'|u u'|o u|o u u'|u|u|u|u|u|u|f u] ; try easy.
now destruct pos.
Qed.

End Convert.

Inductive Transform :=
  | trAtom (f : RAtom -> RAtom) : (forall uv, stable_atom uv f) -> Transform
  | trLeaf (f : bool -> RAtom -> RTree) : (forall uv, stable_atom_tree uv f) -> Transform
  | trBound (f : RExpr -> RExpr) : (forall uv, stable_expr uv f) -> Transform
  | trExpr (f : RExpr -> RExpr) : (forall uv, stable_expr uv f) -> Transform
  | trTree (f : RTree -> RTree) : (forall uv t, convert_tree uv t -> convert_tree uv (f t)) -> Transform.

Definition transform_once tr t :=
  match tr with
  | trAtom f _ => transform_tree_atom f t
  | trLeaf f _ => transform_tree_atom' f t
  | trBound f _ => transform_tree_atom (transform_atom_bound (transform_expr f)) t
  | trExpr f _ => transform_tree_atom (transform_atom_expr (transform_expr f)) t
  | trTree f _ => f t
  end.

Theorem transform_once_correct :
  forall uv tr t,
  convert_tree uv t ->
  convert_tree uv (transform_once tr t).
Proof.
intros uv [f Hf|f Hf|f Hf|f Hf|f Hf] t Ht ; simpl.
now apply transform_tree_atom_correct.
now apply transform_tree_atom'_correct.
apply transform_tree_atom_correct with (2 := Ht).
now apply transform_atom_bound_correct.
apply transform_tree_atom_correct with (2 := Ht).
now apply transform_atom_expr_correct.
now apply Hf.
Qed.

Definition transform :=
  fold_left (fun v t => transform_once t v).

Theorem transform_correct :
  forall l uv t,
  convert_tree uv t ->
  convert_tree uv (transform l t).
Proof.
intros l uv t Ht.
rewrite <- (rev_involutive l).
induction (rev l) as [|h l' Hl] ; simpl.
easy.
unfold transform.
rewrite fold_left_app.
simpl.
apply transform_once_correct.
apply Hl.
Qed.

Definition trans :=
  trAtom change_rel_func change_rel_prop ::
  trAtom change_abs_func change_abs_prop ::
  trBound remove_inv_func remove_inv_prop ::
  trBound gen_float_func gen_float_prop ::
  trBound clean_pow_func clean_pow_prop ::
  trBound merge_float2_func merge_float2_prop ::
  trExpr remove_inv_func remove_inv_prop ::
  trExpr gen_float_func gen_float_prop ::
  trExpr clean_pow_func clean_pow_prop ::
  trLeaf change_format_func change_format_prop ::
  trLeaf remove_unknown_func remove_unknown_prop ::
  trTree simplify_tree simplify_tree_correct ::
  nil.

Theorem prepare_goal :
  forall uv t,
  convert_tree uv (rtNot (transform trans (normalize_tree t false))) ->
  convert_tree uv t.
Proof.
intros uv t.
change (not (convert_tree uv (transform trans (normalize_tree t false))) -> convert_tree uv t).
intros H.
destruct (decidable_tree uv t) as [H'|H'].
easy.
contradict H.
apply transform_correct.
now apply normalize_tree_correct.
Qed.

End Gappa_Private.

Import Gappa_Private.

Declare ML Module "gappatac".

Ltac gappa_prepare :=
  intros ; fold rndNE rndNA in * ;
  gappa_quote ;
  let convert_apply t :=
    match goal with
    | |- (convert_tree ?uv ?g) => t uv g
    end in
  convert_apply ltac:(fun uv g =>
    let rec generalize_list l :=
      match l with
      | (List.cons ?h ?t) => generalize h ; generalize_list t
      | List.nil => clear ; intros
      end in
    generalize_list uv) ;
  convert_apply ltac:(fun uv g => refine (prepare_goal uv g _)) ;
  convert_apply ltac:(fun uv g => let g := eval vm_compute in g in change (convert_tree uv g)).
