Require Import Reals.
Require Import List.
Require Import Fcore_Raux.
Require Import Fcore_defs.
Require Import Fcore_float_prop.
Require Export Gappa_library.

Strategy 1000 [Fcore_generic_fmt.round].

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

Section ListProp.

Variable A : Type.
Variable P : A -> Prop.

Inductive list_prop : list A -> Prop :=
  | Pnil : list_prop nil
  | Pcons x q : P x -> list_prop q -> list_prop (x :: q).

End ListProp.

Inductive UnaryOp : Set :=
  | uoNeg | uoSqrt | uoAbs | uoInv.

Inductive BinaryOp : Set :=
  | boAdd | boSub | boMul | boDiv.

(* represent an expression on real numbers *)
Inductive RExpr :=
  | reUnknown : positive -> RExpr
  | reInteger : Z -> RExpr
  | reFloat2 : Z -> Z -> RExpr
  | reFloat10 : Z -> Z -> RExpr
  | reUnary : UnaryOp -> RExpr -> RExpr
  | reBinary : BinaryOp -> RExpr -> RExpr -> RExpr
  | rePow2 : Z -> RExpr
  | rePow10 : Z -> RExpr
  | reINR : positive -> RExpr
  | reApply : positive -> RExpr -> RExpr.

Scheme Equality for positive.
Scheme Equality for Z.
Scheme Equality for UnaryOp.
Scheme Equality for BinaryOp.
Scheme Equality for RExpr.

(* represent an atomic proposition *)
Inductive RAtom :=
  | raBound : option RExpr -> RExpr -> option RExpr -> RAtom
  | raRel : RExpr -> RExpr -> RExpr -> RExpr -> RAtom
  | raLe : RExpr -> RExpr -> RAtom
  | raEq : RExpr -> RExpr -> RAtom
  | raFalse : RAtom.

Section Convert.

Variable unknown_values : list R.
Variable unknown_functions : list (R -> R).

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
  | rePow2 x =>
    powerRZ 2%R x
  | rePow10 x =>
    powerRZ 10%R x
  | reINR x =>
    INR (nat_of_P x)
  | reApply f x =>
    nth (nat_of_P f) ((fun x => x) :: unknown_functions) (fun x => x) (convert_expr x)
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
  | raFalse => False
  end.

Section ConvertGoal.

Variable gc : RAtom.

(* convert to a complete proposition *)
Fixpoint convert_goal_aux gh : Prop :=
  match gh with
  | h :: gh => convert_atom h -> convert_goal_aux gh
  | nil => convert_atom gc
  end.

End ConvertGoal.

Definition convert_goal g :=
  let '(gh, gc) := g in convert_goal_aux gc gh.

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
    | reApply f x => reApply f (transform_expr x)
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

Section StableAtomNeg.

Definition stable_atom_neg f :=
  forall a, list_prop _ (fun b => convert_atom a -> convert_atom b) (f a).

Variable chg_atom_neg : RAtom -> list RAtom.

Fixpoint transform_goal_neg gh :=
  match gh with
  | h :: gh => chg_atom_neg h ++ (transform_goal_neg gh)
  | nil => nil
  end.

Theorem transform_goal_neg_correct :
  stable_atom_neg chg_atom_neg ->
  forall gh gc, convert_goal_aux gc (transform_goal_neg gh) -> convert_goal_aux gc gh.
Proof.
intros Hn gh gc.
induction gh.
easy.
simpl.
intros H1 H2.
apply IHgh.
clear IHgh.
specialize (Hn a).
induction (chg_atom_neg a).
exact H1.
inversion_clear Hn.
apply IHl.
exact H0.
apply H1.
now apply H.
Qed.

End StableAtomNeg.

Definition stable_atom_pos f :=
  forall a, convert_atom (f a) -> convert_atom a.

Definition stable_goal f :=
  forall gh gc, convert_goal (f gh gc) -> convert_goal (gh, gc).

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
  forall a,
  convert_atom (transform_atom_bound (transform_expr f) a) <-> convert_atom a.
Proof.
now intros f Hf [[l|] e [u|]|x y l u|x y|x y|] ;
  simpl ; split ; repeat rewrite (transform_expr_correct _ Hf).
Qed.

Definition transform_atom_expr f a :=
  match a with
  | raBound l e u => raBound l (f e) u
  | raRel er ex l u => raRel (f er) (f ex) l u
  | _ => a
  end.

Theorem transform_atom_expr_correct :
  forall f,
  stable_expr f ->
  forall a,
  convert_atom (transform_atom_expr (transform_expr f) a) <-> convert_atom a.
Proof.
now intros f Hf [l e u|x y l u|x y|x y|] ;
  simpl ; split ; repeat rewrite (transform_expr_correct _ Hf).
Qed.

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
  | reBinary boMul (reInteger x) (rePow2 y) =>
    reFloat2 x y
  | reBinary boMul (reInteger x) (rePow10 y) =>
    reFloat10 x y
  | reINR x =>
    reInteger (Zpos x)
  | _ => t
  end.

Lemma gen_float_prop :
  stable_expr gen_float_func.
Proof.
intros [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try apply refl_equal.
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
Qed.

(* remove pending powerRZ *)
Definition clean_pow_func t :=
  match t with
  | rePow2 x => reFloat2 1 x
  | rePow10 x => reFloat10 1 x
  | _ => t
  end.

Lemma clean_pow_prop :
  stable_expr clean_pow_func.
Proof.
intros [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try apply refl_equal.
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
intros [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try apply refl_equal ; try exact (H x _).
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
intros [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try apply refl_equal.
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

Ltac nothing := apply Pcons ; try apply Pnil ; intros H ; exact H.
Ltac almost_nothing := apply Pcons ; try apply Pnil ; intros H ; try exact H.

Definition change_abs_pos_func a :=
  match a with
  | raLe (reUnary uoAbs u as u') v => raBound (Some (reFloat2 0 0)) u' (Some v)
  | _ => a
  end.

Lemma change_abs_pos_prop :
  stable_atom_pos change_abs_pos_func.
Proof.
intros [l v u|x y l u|v w|v w|] H ; try exact H.
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try exact H.
destruct o ; try exact H.
exact (proj2 H).
Qed.

Definition change_abs_neg_func a :=
  match a with
  | raLe (reUnary uoAbs u as u') v => raBound (Some (reFloat2 0 0)) u' (Some v) :: nil
  | _ => a :: nil
  end.

Lemma change_abs_neg_prop :
  stable_atom_neg change_abs_neg_func.
Proof.
unfold change_abs_neg_func.
intros [l v u|x y l u|v w|v w|] ; try nothing.
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try nothing.
destruct o ; almost_nothing.
split.
simpl.
unfold float2R.
rewrite F2R_0.
apply Rabs_pos.
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

Definition change_rel_pos_func a :=
  match a with
  | raLe (reUnary uoAbs (reBinary boSub er ex)) (reBinary boMul u (reUnary uoAbs ex')) =>
    if RExpr_beq ex ex' then
      raRel er ex (reUnary uoNeg u) u
    else a
  | _ => a
  end.

Lemma change_rel_pos_prop :
  stable_atom_pos change_rel_pos_func.
Proof.
unfold change_rel_pos_func.
intros [l v u|x y l u|v w|v w|] H ; try exact H.
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try exact H.
destruct o ; try exact H.
destruct x as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try exact H.
destruct o ; try exact H.
destruct w as [u|u|u v|u v|o u|o u v|u|u|u|f u] ; try exact H.
destruct o ; try exact H.
destruct v as [v|v|v w|v w|o v|o v w|v|v|v|f v] ; try exact H.
destruct o ; try exact H.
case_eq (RExpr_beq y v) ; intros Hb.
rewrite <- RExpr_dec_bl with (1 := Hb).
2: now rewrite Hb in H.
simpl.
apply <- change_rel_aux.
now rewrite Hb in H.
Qed.

Definition change_rel_neg_func a :=
  match a with
  | raLe (reUnary uoAbs (reBinary boSub er ex)) (reBinary boMul b (reUnary uoAbs ex')) =>
    if RExpr_beq ex ex' then
      match get_float2_bound b with
      | reFloat2 (Zpos m) e => raRel er ex (reFloat2 (Zneg m) e) (reFloat2 (Zpos m) e) :: nil
      | _ => a :: nil
      end
    else a :: nil
  | _ => a :: nil
  end.

Lemma change_rel_neg_prop :
  stable_atom_neg change_rel_neg_func.
Proof.
unfold change_rel_neg_func.
intros [l v u|x y l u|v w|v w|] ; try nothing.
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try nothing.
destruct o ; try nothing.
destruct x as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try nothing.
destruct o ; try nothing.
destruct w as [u|u|u v|u v|o u|o u v|u|u|u|f u] ; try nothing.
destruct o ; try nothing.
destruct v as [v|v|v w|v w|o v|o v w|v|v|v|f v] ; try nothing.
destruct o ; try nothing.
case_eq (RExpr_beq y v) ; intros Hb ; try nothing.
assert (H1 := get_float2_bound_correct u).
destruct (get_float2_bound u) as [u1|u1|m e|u1 u2|o u1|o u1 u2|u1|u1|u1|f u1] ; try nothing.
destruct m as [|m|m] ; almost_nothing.
simpl.
change (Float2 (Zneg m) e) with (Gappa_dyadic.Fopp2 (Float2 (Zpos m) e)).
rewrite Gappa_dyadic.Fopp2_correct.
apply -> change_rel_aux.
split.
now apply (Gappa_dyadic.Fpos0_correct (Float2 (Zpos m) e)).
rewrite <- RExpr_dec_bl with (1 := Hb) in H.
simpl in H1.
now rewrite H1.
Qed.

Definition remove_unknown_pos_func a :=
  match a with
  | raBound (Some l) _ (Some u) =>
    match l with
    | reInteger _
    | reFloat2 _ _ =>
      match u with
      | reInteger _
      | reFloat2 _ _ => a
      | _ => raFalse
      end
    | _ => raFalse
    end
  | raRel _ _ (reFloat2 _ _) (reFloat2 _ _) => a
  | raEq _ _ => a
  | _ => raFalse
  end.

Lemma remove_unknown_pos_prop :
  stable_atom_pos remove_unknown_pos_func.
Proof.
unfold remove_unknown_pos_func.
intros [[l|] v [u|]|v w l u|v w|v w|] ; try easy.
destruct l as [xl|xl|xl yl|xl yl|ol xl|ol xl yl|xl|xl|xl|fl xl] ; try easy ;
  destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|fu xu] ; easy.
destruct l as [l|l|l l'|l l'|o l|o l l'|l|l|l|f l] ; try easy.
destruct u as [u|u|u u'|u u'|o u|o u u'|u|u|u|f u] ; try easy.
Qed.

Definition remove_unknown_neg_func a :=
  match a with
  | raBound (Some l) _ (Some u) =>
    match l with
    | reInteger _
    | reFloat2 _ _ =>
      match u with
      | reInteger _
      | reFloat2 _ _ => a :: nil
      | _ => nil
      end
    | _ => nil
    end
  | raBound _ _ _ => a :: nil
  | raRel _ _ (reFloat2 _ _) (reFloat2 _ _) => a :: nil
  | raEq _ _ => a :: nil
  | _ => nil
  end.

Lemma remove_unknown_neg_prop :
  stable_atom_neg remove_unknown_neg_func.
Proof.
unfold remove_unknown_neg_func.
intros [[l|] v [u|]|v w l u|v w|v w|] ; try nothing ; try apply Pnil.
destruct l as [xl|xl|xl yl|xl yl|ol xl|ol xl yl|xl|xl|xl|fl xl] ; try apply Pnil ;
  destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|fu xu] ; try apply Pnil ;
  nothing.
destruct l as [l|l|l l'|l l'|o l|o l l'|l|l|l|f l] ; try apply Pnil.
destruct u as [u|u|u u'|u u'|o u|o u u'|u|u|u|f u] ; try apply Pnil ; nothing.
Qed.

Definition Gmax_lower x y :=
  match x, y with
  | None, _ => Some y
  | _, None => Some x
  | Some (reFloat2 xm xe as x'), Some (reFloat2 ym ye as y') =>
    Some (Some (if Gappa_dyadic.Fle2 (Float2 xm xe) (Float2 ym ye) then y' else x'))
  | _, _ => None
  end.

Definition Gmin_upper x y :=
  match x, y with
  | None, _ => Some y
  | _, None => Some x
  | Some (reFloat2 xm xe as x'), Some (reFloat2 ym ye as y') =>
    Some (Some (if Gappa_dyadic.Fle2 (Float2 xm xe) (Float2 ym ye) then x' else y'))
  | _, _ => None
  end.

Lemma Gmax_lower_correct :
  forall e l1 l2,
  convert_atom (raBound l1 e None) ->
  convert_atom (raBound l2 e None) ->
  match Gmax_lower l1 l2 with
  | Some l => convert_atom (raBound l e None)
  | _ => True
  end.
Proof.
intros e l1 l2 H1 H2.
case_eq (Gmax_lower l1 l2) ; try easy.
intros o Hl.
destruct l1 as [l1|] ; simpl in H1 ; try easy.
destruct l2 as [l2|] ; simpl in H2 ; try easy.
destruct l1 as [xl1|xl1|xl1 yl1|xl1 yl1|ol1 xl1|ol1 xl1 yl1|xl1|xl1|xl1|fl1 xl1] ; try discriminate Hl.
destruct l2 as [xl2|xl2|xl2 yl2|xl2 yl2|ol2 xl2|ol2 xl2 yl2|xl2|xl2|xl2|fl2 xl2] ; try discriminate Hl.
inversion_clear Hl.
now destruct (Gappa_dyadic.Fle2_spec (Float2 xl1 yl1) (Float2 xl2 yl2)).
destruct l1 as [xl1|xl1|xl1 yl1|xl1 yl1|ol1 xl1|ol1 xl1 yl1|xl1|xl1|xl1|fl1 xl1] ; now inversion_clear Hl.
revert H2.
now inversion_clear Hl.
Qed.

Lemma Gmin_upper_correct :
  forall e u1 u2,
  convert_atom (raBound None e u1) ->
  convert_atom (raBound None e u2) ->
  match Gmin_upper u1 u2 with
  | Some u => convert_atom (raBound None e u)
  | _ => True
  end.
Proof.
intros e u1 u2 H1 H2.
case_eq (Gmin_upper u1 u2) ; try easy.
intros o Hu.
destruct u1 as [u1|] ; simpl in H1 ; try easy.
destruct u2 as [u2|] ; simpl in H2 ; try easy.
destruct u1 as [xu1|xu1|xu1 yu1|xu1 yu1|ou1 xu1|ou1 xu1 yu1|xu1|xu1|xu1|fu1 xu1] ; try discriminate Hu.
destruct u2 as [xu2|xu2|xu2 yu2|xu2 yu2|ou2 xu2|ou2 xu2 yu2|xu2|xu2|xu2|fu2 xu2] ; try discriminate Hu.
inversion_clear Hu.
now destruct (Gappa_dyadic.Fle2_spec (Float2 xu1 yu1) (Float2 xu2 yu2)).
destruct u1 as [xu1|xu1|xu1 yu1|xu1 yu1|ou1 xu1|ou1 xu1 yu1|xu1|xu1|xu1|fu1 xu1] ; now inversion_clear Hu.
revert H2.
now inversion_clear Hu.
Qed.

Lemma raBound_split :
  forall e l u,
  convert_atom (raBound l e u) <->
  convert_atom (raBound l e None) /\ convert_atom (raBound None e u).
Proof.
intros e [l|] [u|] ; split ; (intros (H1,H2) || intros H) ; try split ; easy.
Qed.

Lemma Gminmax_correct :
  forall e l1 u1 l2 u2,
  convert_atom (raBound l1 e u1) ->
  convert_atom (raBound l2 e u2) ->
  match Gmax_lower l1 l2, Gmin_upper u1 u2 with
  | Some l, Some u => convert_atom (raBound l e u)
  | _, _ => True
  end.
Proof.
intros e l1 u1 l2 u2 H1 H2.
destruct (proj1 (raBound_split _ _ _) H1) as (H1l,H1u).
destruct (proj1 (raBound_split _ _ _) H2) as (H2l,H2u).
generalize (Gmax_lower_correct _ _ _ H1l H2l).
destruct (Gmax_lower l1 l2) as [l|] ; try easy.
intros Hl.
generalize (Gmin_upper_correct _ _ _ H1u H2u).
destruct (Gmin_upper u1 u2) as [u|] ; try easy.
intros Hu.
apply <- raBound_split ; now split.
Qed.

Section MergeHypsFunc1.

Variable e : RExpr.
Variable l u : option RExpr.

Fixpoint merge_hyps_func_aux1 gh :=
  match gh with
  | nil => raBound l e u :: nil
  | raBound l' e' u' as h' :: gh =>
    if RExpr_beq e e' then
      match Gmax_lower l l', Gmin_upper u u' with
      | Some l'', Some u'' => raBound l'' e' u'' :: gh
      | _, _ => h' :: merge_hyps_func_aux1 gh
      end
    else h' :: merge_hyps_func_aux1 gh
  | h' :: gh => h' :: merge_hyps_func_aux1 gh
  end.

Lemma merge_hyps_func_aux1_correct :
  forall gh gc,
  convert_goal_aux gc (merge_hyps_func_aux1 gh) -> convert_goal_aux gc (raBound l e u :: gh).
Proof.
intros gh gc.
induction gh.
easy.
intros H H1 H2.
change (convert_goal_aux gc gh).
destruct a as [l' v u'|v w l' u'|v w|v w|] ; try (apply IHgh ; try apply H ; easy).
simpl in H.
case_eq (RExpr_beq e v) ; intros H3 ; rewrite H3 in H.
rewrite (RExpr_dec_bl _ _ H3) in H1, IHgh.
generalize (Gminmax_correct _ _ _ _ _ H1 H2).
destruct (Gmax_lower l l') as [l''|].
destruct (Gmin_upper u u') as [u''|].
intros H4.
now apply H.
intros _.
apply IHgh.
now apply H.
easy.
intros _.
apply IHgh.
now apply H.
easy.
apply IHgh.
now apply H.
easy.
Qed.

End MergeHypsFunc1.

Fixpoint merge_hyps_func_aux2 gh :=
  match gh with
  | raBound l e u :: gh => (merge_hyps_func_aux1 e l u gh)
  | h :: gh => h :: merge_hyps_func_aux2 gh
  | nil => nil
  end.

Lemma merge_hyps_func_aux2_correct :
  forall gh gc,
  convert_goal_aux gc (merge_hyps_func_aux2 gh) -> convert_goal_aux gc gh.
Proof.
intros gh gc.
induction gh.
easy.
intros H1 H2.
change (convert_goal_aux gc gh).
destruct a as [l' v u'|v w l' u'|v w|v w|] ; try (apply IHgh ; apply H1 ; apply H2).
simpl in H1.
now apply (merge_hyps_func_aux1_correct v l' u' gh gc).
Qed.

Definition merge_hyps_func gh (gc : RAtom) :=
  (merge_hyps_func_aux2 gh, gc).

Lemma merge_hyps_prop :
  stable_goal merge_hyps_func.
Proof.
intros gh gc.
unfold merge_hyps_func.
apply merge_hyps_func_aux2_correct.
Qed.

Theorem contradict_goal :
  forall gh gc,
  convert_goal_aux raFalse gh -> convert_goal (gh, gc).
Proof.
intros gh gc.
induction gh.
easy.
intros H1 H2.
apply IHgh.
now apply H1.
Qed.

End Convert.

Inductive TG :=
  | TGall f : (forall uv uf, stable_goal uv uf f) -> TG
  | TGneg (f : RAtom -> list RAtom) : (forall uv uf, stable_atom_neg uv uf f) -> TG
  | TGpos (f : RAtom -> RAtom) : (forall uv uf, stable_atom_pos uv uf f) -> TG
  | TGbound (f : RExpr -> RExpr) : (forall uv uf, stable_expr uv uf f) -> TG
  | TGexpr (f : RExpr -> RExpr) : (forall uv uf, stable_expr uv uf f) -> TG.

Definition transform_goal_once t g :=
  let '(gh, gc) := g in
  match t with
  | TGall f _ => f gh gc
  | TGneg f _ => (transform_goal_neg f gh, gc)
  | TGpos f _ => (gh, f gc)
  | TGbound f _ =>
    let f' := transform_atom_bound (transform_expr f) in
    (map f' gh, f' gc)
  | TGexpr f _ =>
    let f' := transform_atom_expr (transform_expr f) in
    (map f' gh, f' gc)
  end.

Theorem transform_goal_once_correct :
  forall uv uf t g,
  convert_goal uv uf (transform_goal_once t g) ->
  convert_goal uv uf g.
Proof.
intros uv uf [f Hf|f Hf|f Hf|f Hf|f Hf] (gh, gc) ; simpl.
intros H.
now apply Hf.
intros H.
now apply transform_goal_neg_correct with f.
induction gh.
apply Hf.
intros H1 H2.
apply IHgh.
now apply H1.
induction gh.
intros H.
now apply -> (transform_atom_bound_correct uv uf f).
intros H1 H2.
apply IHgh.
apply H1.
now apply <- transform_atom_bound_correct.
induction gh.
intros H.
now apply -> (transform_atom_expr_correct uv uf f).
intros H1 H2.
apply IHgh.
apply H1.
now apply <- transform_atom_expr_correct.
Qed.

Definition transform_goal :=
  fold_left (fun v t => transform_goal_once t v).

Theorem transform_goal_correct :
  forall l uv uf g,
  convert_goal uv uf (transform_goal l g) -> convert_goal uv uf g.
Proof.
intros l uv uf.
rewrite <- (rev_involutive l).
induction (rev l) ; intros g ; simpl.
easy.
unfold transform_goal.
rewrite fold_left_app.
simpl.
intros H.
apply IHl0.
now apply transform_goal_once_correct in H.
Qed.

Definition trans :=
  TGneg change_rel_neg_func change_rel_neg_prop ::
  TGpos change_rel_pos_func change_rel_pos_prop ::
  TGneg change_abs_neg_func change_abs_neg_prop ::
  TGpos change_abs_pos_func change_abs_pos_prop ::
  TGbound remove_inv_func remove_inv_prop ::
  TGbound gen_float_func gen_float_prop ::
  TGbound clean_pow_func clean_pow_prop ::
  TGbound merge_float2_func merge_float2_prop ::
  TGexpr remove_inv_func remove_inv_prop ::
  TGexpr gen_float_func gen_float_prop ::
  TGexpr clean_pow_func clean_pow_prop ::
  TGneg remove_unknown_neg_func remove_unknown_neg_prop ::
  TGpos remove_unknown_pos_func remove_unknown_pos_prop ::
  TGall merge_hyps_func merge_hyps_prop ::
  nil.

Declare ML Module "gappatac".

Ltac gappa_prepare :=
  intros ; subst ;
  gappa_quote ;
  let convert_apply t :=
    match goal with
    | |- (convert_goal ?uv ?uf ?g) => t uv uf g
    end in
  convert_apply ltac:(fun uv _ g =>
    let rec generalize_list l :=
      match l with
      | (List.cons ?h ?t) => generalize h ; generalize_list t
      | List.nil => clear ; intros
      end in
    generalize_list uv) ;
  convert_apply ltac:(fun uv uf g => refine (transform_goal_correct trans uv uf g _)) ;
  convert_apply ltac:(fun uv uf g => let g := eval vm_compute in g in change (convert_goal uv uf g)).
