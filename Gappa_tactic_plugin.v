Require Import Reals.
Require Import List.
Require Export Gappa_library.
Require Import Gappa_integer.

Definition gappa_rounding (f : R -> float2) (x : R) : R := f x.
Strategy 1000 [rounding_fixed rounding_float]
         1001 [gappa_rounding]
         1002 [Gappa_round.round_extension].

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
change (Z2R (Zpos x)) with (float2R (Float2 (Zpos x) 0%Z)).
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
intros [|m|m] e ; simpl.
rewrite (Gappa_dyadic.float2_zero e).
apply refl_equal.
generalize (float2_of_pos_correct m).
destruct (float2_of_pos m) as (m1, e1).
intros H.
rewrite Zplus_comm.
rewrite <- (Zmult_1_r m1).
change (Gappa_dyadic.Fmult2 (Float2 m1 e1) (Float2 1 e) = Float2 (Zpos m) e :>R).
rewrite Gappa_dyadic.Fmult2_correct.
rewrite Gappa_round_aux.float2_pow2.
rewrite H.
apply sym_eq.
exact (F2R_split _ (Zpos m) e).
generalize (float2_of_pos_correct m).
destruct (float2_of_pos m) as (m1, e1).
intros H.
rewrite Zplus_comm.
rewrite <- (Zmult_1_r m1).
change (Gappa_dyadic.Fopp2 (Gappa_dyadic.Fmult2 (Float2 m1 e1) (Float2 1 e)) = Float2 (Zneg m) e :>R).
rewrite Gappa_dyadic.Fopp2_correct.
rewrite Gappa_dyadic.Fmult2_correct.
rewrite Gappa_round_aux.float2_pow2.
rewrite H.
rewrite <- Ropp_mult_distr_l_reverse.
apply sym_eq.
exact (F2R_split _ (Zneg m) e).
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

(* represent an atomic proposition *)
Inductive RAtom :=
  | raBound : option RExpr -> RExpr -> option RExpr -> RAtom
  | raLe : RExpr -> RExpr -> RAtom
  | raEq : RExpr -> RExpr -> RAtom
  | raFalse : RAtom.

(* represent a complete proposition *)
Definition RGoal := (list RAtom * RAtom)%type.

Section Convert.

Variable unknown_values : list R.
Variable unknown_functions : list (R -> R).

(* convert to an expression on real numbers *)
Fixpoint convert_expr (t : RExpr) : R :=
  match t with
  | reUnknown x =>
    nth (nat_of_P x) (R0 :: unknown_values) R0
  | reInteger x => Z2R x
  | reFloat2 x y => F2R 2 x y
  | reFloat10 x y => F2R 10 x y
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
  | raBound None _ None => False
  | raBound (Some l) e None => (convert_expr l <= convert_expr e)%R
  | raBound None e (Some u) => (convert_expr e <= convert_expr u)%R
  | raBound (Some l) e (Some u) => (convert_expr l <= convert_expr e <= convert_expr u)%R
  | raLe x y => (convert_expr x <= convert_expr y)%R
  | raEq x y => (convert_expr x = convert_expr y)%R
  | raFalse => False
  end.

(* convert to a complete proposition *)
Definition convert_goal (g : RGoal) : Prop :=
  fold_right (fun a (r : Prop) => convert_atom a -> r) (convert_atom (snd g)) (fst g).

Section RecursiveTransform.

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

Definition stable_atom_neg f :=
  forall a, list_prop _ (fun b => convert_atom a -> convert_atom b) (f a).

Variable chg_atom_neg : RAtom -> list RAtom.

Definition transform_goal_neg (g : RGoal) :=
  let '(c, g) := g in (fold_right (fun a r => chg_atom_neg a ++ r) nil c, g).

Theorem transform_goal_neg_correct :
  stable_atom_neg chg_atom_neg ->
  forall g, convert_goal (transform_goal_neg g) -> convert_goal g.
Proof.
intros Hn (c, g).
simpl.
induction c.
easy.
intros H1 H2.
apply IHc.
clear IHc.
specialize (Hn a).
simpl in H1.
induction (chg_atom_neg a).
exact H1.
inversion_clear Hn.
apply IHl.
exact H0.
apply H1.
now apply H.
Qed.

Definition stable_atom_pos f :=
  forall a, convert_atom (f a) -> convert_atom a.

Variable chg_atom_pos : RAtom -> RAtom.

Definition transform_goal_pos (g : RGoal) :=
  let '(c, g) := g in (c, chg_atom_pos g).

Theorem transform_goal_pos_correct :
  stable_atom_pos chg_atom_pos ->
  forall g, convert_goal (transform_goal_pos g) -> convert_goal g.
Proof.
intros Hp (c, g).
simpl.
induction c.
exact (Hp g).
intros H1 H2.
apply IHc.
now apply H1.
Qed.

End RecursiveTransform.

Definition transform_atom_bound f a :=
  match a with
  | raBound (Some l) e (Some u) => raBound (Some (f l)) e (Some (f u))
  | raBound (Some l) e None => raBound (Some (f l)) e None
  | raBound None e (Some u) => raBound None e (Some (f u))
  | _ => a
  end.

Theorem transform_atom_bound_correct :
  forall f,
  stable_expr f ->
  forall a,
  convert_atom (transform_atom_bound (transform_expr f) a) <-> convert_atom a.
Proof.
now intros f Hf [[l|] e [u|]|x y|x y|] ;
  simpl ; split ; repeat rewrite (transform_expr_correct _ Hf).
Qed.

Definition transform_atom_expr f a :=
  match a with
  | raBound l e u => raBound l (f e) u
  | _ => a
  end.

Theorem transform_atom_expr_correct :
  forall f,
  stable_expr f ->
  forall a,
  convert_atom (transform_atom_expr (transform_expr f) a) <-> convert_atom a.
Proof.
now intros f Hf [l e u|x y|x y|] ;
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
unfold float2R.
rewrite F2R_split.
apply refl_equal.
(* . x * 10^y *)
simpl.
unfold float10R.
rewrite F2R_split.
apply refl_equal.
(* . x / 2*2*2*2 *)
destruct z0 ; try apply refl_equal.
generalize (float2_of_pos_correct p).
simpl.
destruct (float2_of_pos p) as ([|[m|m|]|m], [|e|e]) ; intros H ; try apply refl_equal.
rewrite <- H.
unfold convert_expr.
unfold float2R.
do 2 rewrite F2R_split.
simpl.
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
apply Gappa_round_aux.float2_pow2.
simpl.
unfold float10R.
rewrite F2R_split.
rewrite Rmult_1_l.
apply refl_equal.
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
(* unary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
simpl.
rewrite H.
change (- F2R 2 z z0)%R with (- float2R (Float2 z z0))%R.
now rewrite <- Gappa_dyadic.Fopp2_correct.
(* binary ops *)
destruct o ; try apply refl_equal.
destruct x ; try apply refl_equal.
destruct y ; try apply refl_equal.
simpl.
rewrite H.
change (F2R 2 z z0 * F2R 2 z1 z2)%R with (float2R (Float2 z z0) * float2R (Float2 z1 z2))%R.
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

Definition change_eq_pos_func a :=
  match a with
  | raEq u v => raBound (Some (reFloat2 0 0)) (reBinary boSub u v) (Some (reFloat2 0 0))
  | _ => a
  end.

Lemma change_eq_pos_prop :
  stable_atom_pos change_eq_pos_func.
Proof.
intros [l v u|x y|x y|] H ; try exact H.
apply Rle_antisym.
apply Rplus_le_reg_l with (- convert_expr y)%R.
rewrite Rplus_opp_l.
rewrite Rplus_comm.
apply H.
apply Ropp_le_cancel.
apply Rplus_le_reg_l with (convert_expr x).
rewrite Rplus_opp_r.
apply H.
Qed.

Definition change_eq_neg_func a :=
  match a with
  | raEq u v => raBound (Some (reFloat2 0 0)) (reBinary boSub u v) (Some (reFloat2 0 0)) :: nil
  | _ => a :: nil
  end.

Lemma change_eq_neg_prop :
  stable_atom_neg change_eq_neg_func.
Proof.
unfold change_eq_neg_func.
intros [l v u|x y|x y|] ; apply Pcons ; try apply Pnil ; intros H ; try exact H.
simpl.
rewrite H.
unfold Rminus.
rewrite Rplus_opp_r.
split ; apply Rle_refl.
Qed.

Definition change_abs_pos_func a :=
  match a with
  | raLe (reUnary uoAbs u as u') v => raBound (Some (reFloat2 0 0)) u' (Some v)
  | _ => a
  end.

Lemma change_abs_pos_prop :
  stable_atom_pos change_abs_pos_func.
Proof.
intros [l v u|v w|v w|] H ; try exact H.
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
intros [l v u|v w|v w|] ; try (apply Pcons ; try apply Pnil ; intros H ; exact H).
destruct v as [x|x|x y|x y|o x|o x y|x|x|x|f x] ; try (apply Pcons ; try apply Pnil ; intros H ; exact H).
destruct o ; apply Pcons ; try apply Pnil ; intros H ; try exact H.
split.
apply Rabs_pos.
exact H.
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
  | _ => raFalse
  end.

Lemma remove_unknown_pos_prop :
  stable_atom_pos remove_unknown_pos_func.
Proof.
unfold remove_unknown_pos_func.
intros [[l|] v [u|]|v w|v w|] ; try (apply Pcons ; try apply Pnil ; intros H ; exact H) ; try easy.
destruct l as [xl|xl|xl yl|xl yl|ol xl|ol xl yl|xl|xl|xl|fl xl] ; try easy ;
  destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|fu xu] ; easy.
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
  | _ => nil
  end.

Lemma remove_unknown_neg_prop :
  stable_atom_neg remove_unknown_neg_func.
Proof.
unfold remove_unknown_neg_func.
intros [[l|] v [u|]|v w|v w|] ; try (apply Pcons ; try apply Pnil ; intros H ; exact H) ; try apply Pnil.
destruct l as [xl|xl|xl yl|xl yl|ol xl|ol xl yl|xl|xl|xl|fl xl] ; try apply Pnil ;
  destruct u as [xu|xu|xu yu|xu yu|ou xu|ou xu yu|xu|xu|xu|fu xu] ; try apply Pnil ;
  apply Pcons ; try apply Pnil ; intros H ; exact H.
Qed.

End Convert.

Inductive TG :=
  | TGneg (f : RAtom -> list RAtom) : (forall uv uf, stable_atom_neg uv uf f) -> TG
  | TGpos (f : RAtom -> RAtom) : (forall uv uf, stable_atom_pos uv uf f) -> TG
  | TGbound (f : RExpr -> RExpr) : (forall uv uf, stable_expr uv uf f) -> TG
  | TGexpr (f : RExpr -> RExpr) : (forall uv uf, stable_expr uv uf f) -> TG.

Definition transform_goal_once t g :=
  match t with
  | TGneg f _ => transform_goal_neg f g
  | TGpos f _ => transform_goal_pos f g
  | TGbound f _ =>
    let f' := transform_atom_bound (transform_expr f) in
    let '(c, g) := g in (map f' c, f' g)
  | TGexpr f _ =>
    let f' := transform_atom_expr (transform_expr f) in
    let '(c, g) := g in (map f' c, f' g)
  end.

Theorem transform_goal_once_correct :
  forall uv uf t g,
  convert_goal uv uf (transform_goal_once t g) -> convert_goal uv uf g.
Proof.
intros uv uf [f Hf|f Hf|f Hf|f Hf] (c, g) ; simpl.
intros H.
now apply transform_goal_neg_correct with f.
intros H.
now apply transform_goal_pos_correct with f.
induction c.
unfold convert_goal. simpl.
now apply -> transform_atom_bound_correct.
unfold convert_goal. simpl.
intros H1 H2.
apply IHc.
apply H1.
now apply <- transform_atom_bound_correct.
induction c.
unfold convert_goal. simpl.
now apply -> transform_atom_expr_correct.
unfold convert_goal. simpl.
intros H1 H2.
apply IHc.
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
  TGneg change_eq_neg_func change_eq_neg_prop ::
  TGpos change_eq_pos_func change_eq_pos_prop ::
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
