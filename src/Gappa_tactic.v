Require Import Reals.
Require Import List.
Require Import Flocq.Core.Core.
Require Export Gappa_library.

Strategy 1000 [Generic_fmt.round].

Module Gappa_Private.

(* factor an integer into odd*2^e *)
Definition float2_of_pos x :=
  let fix aux (m : positive) e { struct m } :=
    match m with
    | xO p => aux p (Z.succ e)
    | _ => Float2 (Zpos m) e
    end in
  aux x Z0.

Lemma float2_of_pos_correct :
  forall x, float2R (float2_of_pos x) = IZR (Zpos x).
Proof.
intros x.
unfold float2_of_pos.
rewrite <- (Rmult_1_r (IZR (Zpos x))).
change (IZR (Zpos x) * 1)%R with (float2R (Float2 (Zpos x) 0%Z)).
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
rewrite <- (float2_of_pos_correct m).
destruct (float2_of_pos m) as (m1, e1).
simpl.
rewrite Zplus_comm.
now rewrite bpow_plus, <- Rmult_assoc.
change (IZR (Zneg m)) with (- IZR (Zpos m))%R.
rewrite <- (float2_of_pos_correct m).
destruct (float2_of_pos m) as (m1, e1).
simpl.
rewrite Zplus_comm.
rewrite bpow_plus, <- Rmult_assoc.
now rewrite opp_IZR, Ropp_mult_distr_l_reverse.
Qed.

Inductive UnaryOp : Set :=
  | uoNeg | uoSqrt | uoAbs | uoInv.

Inductive BinaryOp : Set :=
  | boAdd | boSub | boMul | boDiv.

Inductive Format : Set :=
  | fFixed : Z -> Format
  | fFloat : Z -> Z -> Format
  | fFloatx : Z -> Format.

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
  | raGeneric : Format -> RExpr -> RAtom
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

Definition convert_exp (f : Format) : Z -> Z :=
  match f with
  | fFloat e p => FLT_exp e p
  | fFloatx p => FLX_exp p
  | fFixed e => FIX_exp e
  end.

Definition convert_format (f : Format) : R -> Prop :=
  match f with
  | fFloat e p => FLT_format radix2 e p
  | fFloatx p => FLX_format radix2 p
  | fFixed e => FIX_format radix2 e
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
  | reInteger x => IZR x
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
    Generic_fmt.round radix2 (convert_exp f) (convert_mode m) (convert_expr x)
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
  | raGeneric f x => generic_format radix2 (convert_exp f) (convert_expr x)
  | raFormat f x => convert_format f (convert_expr x)
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
Proof with auto with typeclass_instances.
intros [[l|] e [u|]|x y l u|x y|x y|fmt x|fmt x] ; simpl.
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
destruct fmt as [e|e p|p].
simpl.
destruct (Req_EM_T (convert_expr x) (round radix2 (FIX_exp e) rndZR (convert_expr x))) as [H|H].
left.
apply FIX_format_generic.
rewrite H.
apply generic_format_round...
right.
contradict H.
apply sym_eq, round_generic...
now apply generic_format_FIX.
destruct (Z_lt_le_dec 0 p) as [Hp|Hp].
destruct (Req_EM_T (convert_expr x) (round radix2 (FLT_exp e p) rndZR (convert_expr x))) as [H|H].
left.
apply FLT_format_generic.
apply Hp.
rewrite H.
apply generic_format_round...
right.
contradict H.
apply sym_eq, round_generic...
now apply generic_format_FLT.
destruct p.
destruct (Req_EM_T (convert_expr x) 0) as [H|H].
left.
rewrite H.
exists (Float radix2 0 e).
apply sym_eq, F2R_0.
apply eq_refl.
apply Z.le_refl.
right.
intros ((xm,xe),H1,H2,H3).
simpl in H2.
assert (xm = Z0).
clear -H2 ; zify ; omega.
now rewrite H0, F2R_0 in H1.
now elim Hp.
right.
intros ((xm,xe),H1,H2,H3).
apply Zlt_not_le with (1 := H2).
apply Zabs_pos.
destruct (Z_lt_le_dec 0 p) as [Hp|Hp].
destruct (Req_EM_T (convert_expr x) (round radix2 (FLX_exp p) rndZR (convert_expr x))) as [H|H].
left.
apply FLX_format_generic.
apply Hp.
rewrite H.
apply generic_format_round...
right.
contradict H.
apply sym_eq, round_generic...
now apply generic_format_FLX.
destruct p.
destruct (Req_EM_T (convert_expr x) 0) as [H|H].
left.
rewrite H.
exists (Float radix2 0 0).
apply sym_eq, F2R_0.
apply eq_refl.
right.
intros ((xm,xe),H1,H2).
simpl in H2.
assert (xm = Z0).
clear -H2 ; zify ; omega.
now rewrite H0, F2R_0 in H1.
now elim Hp.
right.
intros ((xm,xe),H1,H2).
apply Zlt_not_le with (1 := H2).
apply Zabs_pos.
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
try (intros H ; now apply H).
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
now intros f Hf [[l|] e [u|]|x y l u|x y|x y|fmt x|fmt x] ;
  simpl ; split ; repeat rewrite (transform_expr_correct _ Hf).
Qed.

Definition transform_atom_expr f a :=
  match a with
  | raBound l e u => raBound l (f e) u
  | raRel er ex l u => raRel (f er) (f ex) l u
  | raEq ex ey => raEq (f ex) (f ey)
  | raLe ex ey => raLe (f ex) (f ey)
  | raGeneric fmt e => raGeneric fmt (f e)
  | raFormat fmt e => raFormat fmt (f e)
  end.

Theorem transform_atom_expr_correct :
  forall f,
  stable_expr f ->
  stable_atom (transform_atom_expr (transform_expr f)).
Proof.
now intros f Hf [l e u|x y l u|x y|x y|fmt x|fmt x] ;
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
simpl.
rewrite <- positive_nat_Z.
apply sym_eq, INR_IZR_INZ.
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
rewrite <- (Rmult_1_r (IZR x)).
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
intros [l v u|x y l u|v w|v w|f x|f x] ; try easy.
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

Definition change_le_func a :=
  match a with
  | raLe x y =>
    match get_float2_bound x with
    | reFloat2 _ _ as x => raBound (Some x) y None
    | _ =>
      match get_float2_bound y with
      | reFloat2 _ _ as y => raBound None x (Some y)
      | _ => a
      end
    end
  | _ => a
  end.

Lemma change_le_prop :
  stable_atom change_le_func.
Proof.
intros [l v u|x y l u|v w|v w|f x|f x] ; try easy.
simpl.
assert (Hv := get_float2_bound_correct v).
assert (Hw := get_float2_bound_correct w).
destruct (get_float2_bound v) as [x|x|x y|x y|o x|o x y|x|x|x|x|x|x|f m x] ;
  destruct (get_float2_bound w) as [x'|x'|x' y'|x' y'|o' x'|o' x' y'|x'|x'|x'|x'|x'|x'|f' m' x'] ;
  try easy ; try (now rewrite <- Hw) ; now rewrite <- Hv.
Qed.

Lemma change_rel_aux:
  forall x y b, (0 <= b /\ Rabs (x - y) <= b * Rabs y)%R <-> (exists eps, -b <= eps <= b /\ x = y * (1 + eps))%R.
Proof.
intros x y b.
split.
(* . *)
intros (H1, H2).
destruct (Req_dec y 0) as [Hy|Hy].
exists 0%R.
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
intros [l v u|x y l u|v w|v w|f x|f x] ; try easy.
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
    | raGeneric (fFixed _ as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | raGeneric (fFloat _ (Zpos _) as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | raGeneric (fFloatx (Zpos _) as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | raFormat (fFixed _ as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | raFormat (fFloat _ (Zpos _) as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | raFormat (fFloatx (Zpos _) as fmt) x => if pos then raEq x (reRound fmt mRndNE x) else raEq (reRound fmt mRndNE x) x
    | _ => a
    end in
  if pos then rtAtom a' else rtNot (rtAtom a').

Lemma change_format_prop :
  stable_atom_tree change_format_func.
Proof.
unfold change_format_func.
intros [l v u|x y l u|v w|v w|[em|em [|p|p]|[|p|p]] x|[em|em [|p|p]|[|p|p]] x] pos ; try (case pos ; easy) ; simpl ; intros H.
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
destruct pos ; simpl.
apply sym_eq, round_generic.
apply valid_rnd_N.
exact H.
contradict H.
rewrite <- H.
apply generic_format_round.
now apply FLX_exp_valid.
apply valid_rnd_N.
destruct pos ; simpl.
apply sym_eq, round_generic.
apply valid_rnd_N.
now apply generic_format_FIX.
contradict H.
rewrite <- H.
apply FIX_format_generic.
apply generic_format_round.
apply FIX_exp_valid.
apply valid_rnd_N.
destruct pos ; simpl.
apply sym_eq, round_generic.
apply valid_rnd_N.
apply generic_format_FLT.
exact H.
contradict H.
rewrite <- H.
apply FLT_format_generic.
easy.
apply generic_format_round.
now apply FLT_exp_valid.
apply valid_rnd_N.
destruct pos ; simpl.
apply sym_eq, round_generic.
apply valid_rnd_N.
apply generic_format_FLX.
exact H.
contradict H.
rewrite <- H.
apply FLX_format_generic.
easy.
apply generic_format_round.
now apply FLX_exp_valid.
apply valid_rnd_N.
Qed.

Definition remove_unknown_func (pos : bool) a :=
  match a with
  | raBound l _ u =>
    match l with
    | Some (reFloat2 _ _)
    | None =>
      match u with
      | Some (reFloat2 _ _)
      | None => if pos then rtAtom a else rtNot (rtAtom a)
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
intros [[l|] v [u|]|x y l u|v w|v w|f x|f x] pos ; try (case pos ; easy) ; simpl ; intros H.
destruct l as [xl|xl|xl yl|xl yl|ol xl|ol xl yl|xl|xl|xl|xl|xl|xl|fl xl] ; try easy.
destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|xu|xu|xu|fu xu] ; try easy.
now destruct pos.
destruct l as [l|l|l l'|l l'|o l|o l l'|l|l|l|l|l|l|f l] ; try easy.
now destruct pos.
destruct u as [u|u|u u'|u u'|o u|o u u'|u|u|u|u|u|u|f u] ; try easy.
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
  trAtom change_le_func change_le_prop ::
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
  let rec generalize_all m n l :=
    match l with
    | List.nil => clear
    | List.cons ?h ?q =>
      match n with
      | O =>
        generalize h ; clear ; intro ;
        convert_apply ltac:(fun uv _ => generalize_all (S m) (S m) uv)
      | S ?n => generalize_all m n q
      end
    end in
  convert_apply ltac:(fun uv _ => generalize_all O O uv) ;
  convert_apply ltac:(fun uv g => refine (prepare_goal uv g _)) ;
  convert_apply ltac:(fun uv g => let g := eval vm_compute in g in change (convert_tree uv g)).

Ltac gappa := abstract (gappa_prepare ; gappa_internal).
