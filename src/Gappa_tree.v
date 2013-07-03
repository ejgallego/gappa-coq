Require Import Reals List Bool.
Require Import Gappa_common.

Definition index := nat.
Definition realmap := list R.
Definition get rm n := nth n rm R0.

Fixpoint index_eq x y :=
  match x, y with
  | O, O => true
  | S x, S y => index_eq x y
  | _, _ => false
  end.

Lemma index_eq_correct :
  forall x y, index_eq x y = true -> x = y.
Proof.
induction x.
now destruct y.
destruct y.
easy.
intro H.
now rewrite (IHx y).
Qed.

Inductive pos_atom :=
  | Abnd : index -> FF -> pos_atom
  | Aabs : index -> FF -> pos_atom
  | Arel : index -> index -> FF -> pos_atom
  | Afix : index -> Z -> pos_atom
  | Aflt : index -> positive -> pos_atom
  | Anzr : index -> pos_atom
  | Aeql : index -> index -> pos_atom.

Definition interp_pos_atom a rm :=
  match a with
  | Abnd x xi => BND (get rm x) xi
  | Aabs x xi => ABS (get rm x) xi
  | Arel x y xi => REL (get rm x) (get rm y) xi
  | Afix x xc => FIX (get rm x) xc
  | Aflt x xc => FLT (get rm x) xc
  | Anzr x => NZR (get rm x)
  | Aeql x y => get rm x = get rm y
  end.

Definition atom := (pos_atom * bool)%type.

Definition interp_atom a rm :=
  match a with
  | (a,true) => interp_pos_atom a rm
  | (a,false) => not (interp_pos_atom a rm)
  end.

Inductive tree :=
  | Ttree : bool -> list atom -> list tree -> tree.

Fixpoint interp_tree t rm :=
  match t with
  | Ttree cnj la lt =>
    let ft := fix ft lt :=
      match lt with
      | nil => if cnj then True else False
      | t :: nil => interp_tree t rm
      | t :: lt => (if cnj then and else or) (interp_tree t rm) (ft lt)
      end in
    let fa := fix fa la :=
      match la, lt with
      | nil, _ => ft lt
      | a :: nil, nil => interp_atom a rm
      | a :: la, _ => (if cnj then and else or) (interp_atom a rm) (fa la)
      end in
    fa la
  end.

Fixpoint interp_list {A} (cnj:bool) (l : list A) interp :=
  match l with
  | nil => if cnj then True else False
  | x :: l =>
    (if cnj then and else or) (interp x) (interp_list cnj l interp)
  end.

Definition interp_list_atom cnj la rm :=
  interp_list cnj la (fun a => interp_atom a rm).

Definition interp_list_tree cnj lt rm :=
  interp_list cnj lt (fun t => interp_tree t rm).

Definition interp_lists (cnj:bool) la lt rm :=
  (if cnj then and else or) (interp_list_atom cnj la rm) (interp_list_tree cnj lt rm).

Lemma interp_tree_correct :
  forall t rm,
  interp_tree t rm <->
  match t with
  | Ttree cnj la lt => interp_lists cnj la lt rm
  end.
Proof.
intros ([|],la,lt) rm.
(* conjunction *)
revert la.
fix 1.
intros [|a la].
clear interp_tree_correct.
revert lt.
fix 1.
intros [|t lt].
clear interp_tree_correct.
easy.
specialize (interp_tree_correct lt).
destruct lt as [|t' lt].
clear interp_tree_correct.
split.
split.
exact I.
split.
exact H.
exact I.
intros (_,(H,_)).
exact H.
split.
split.
exact I.
split.
exact (proj1 H).
apply interp_tree_correct.
exact (proj2 H).
intros (_,H).
split.
exact (proj1 H).
apply interp_tree_correct.
split.
exact I.
exact (proj2 H).
specialize (interp_tree_correct la).
destruct la as [|a' la].
destruct lt as [|t lt].
split.
split.
split.
exact H.
exact I.
exact I.
intros ((H,_),_).
exact H.
split.
split.
split.
exact (proj1 H).
exact I.
apply interp_tree_correct.
exact (proj2 H).
intros ((H1,_),H2).
split.
exact H1.
apply interp_tree_correct.
split.
exact I.
exact H2.
split.
split.
split.
exact (proj1 H).
apply interp_tree_correct.
exact (proj2 H).
apply interp_tree_correct.
exact (proj2 H).
intros ((H1,H2),H3).
split.
exact H1.
apply interp_tree_correct.
split.
exact H2.
exact H3.
(* disjunction *)
revert la.
fix 1.
intros [|a la].
clear interp_tree_correct.
revert lt.
fix 1.
intros [|t lt].
clear interp_tree_correct.
split.
intros [].
intros [[]|[]].
specialize (interp_tree_correct lt).
destruct lt as [|t' lt].
clear interp_tree_correct.
split.
intros H.
right.
left.
exact H.
intros [[]|[H|[]]].
exact H.
split.
intros H.
right.
destruct H as [H|H].
left.
exact H.
destruct (proj1 interp_tree_correct H) as [[]|H'].
right.
exact H'.
intros [[]|[H|H]].
left.
exact H.
right.
apply (proj2 interp_tree_correct).
right.
exact H.
specialize (interp_tree_correct la).
destruct la as [|a' la].
destruct lt as [|t' lt].
split.
intros H.
left.
left.
exact H.
intros [[H|[]]|[]].
exact H.
split.
intros [H|H].
left.
left.
exact H.
destruct (proj1 interp_tree_correct H) as [[]|H'].
right.
exact H'.
intros [[H|[]]|H].
left.
exact H.
right.
apply interp_tree_correct.
right.
exact H.
split.
intros [H|H].
left.
left.
exact H.
destruct (proj1 interp_tree_correct H) as [H'|H'].
left.
right.
exact H'.
right.
exact H'.
intros [[H|H]|H].
left.
exact H.
right.
apply interp_tree_correct.
left.
exact H.
right.
apply interp_tree_correct.
right.
exact H.
Qed.

Lemma interp_list_app :
  forall {A} cnj (l1 l2 : list A) interp,
  interp_list cnj (app l1 l2) interp <->
  (if cnj then and else or) (interp_list cnj l1 interp) (interp_list cnj l2 interp).
Proof.
intros A [|] l1 l2 rm.
(* conjunction *)
induction l1.
split.
now split.
now intros (_,H).
split.
intros (H1,H2).
split.
split.
exact H1.
now apply IHl1.
now apply IHl1.
intros ((H1,H2),H3).
split.
exact H1.
apply IHl1.
now split.
(* disjunction *)
induction l1.
split.
intros H.
now right.
now intros [[]|H].
split.
intros [H|H].
left.
now left.
destruct (proj1 IHl1 H) as [H'|H'].
left.
now right.
now right.
intros [[H|H]|H].
now left.
right.
apply IHl1.
now left.
right.
apply IHl1.
now right.
Qed.

Lemma interp_lists_app :
  forall cnj la1 la2 lt1 lt2 rm,
  interp_lists cnj (app la1 la2) (app lt1 lt2) rm <->
  (if cnj then and else or) (interp_lists cnj la1 lt1 rm) (interp_lists cnj la2 lt2 rm).
Proof.
intros [|] la1 la2 lt1 lt2 rm.
split.
intros (H1,H2).
refine ((fun H1 H2 => match H1, H2 with (conj H1a H1b),(conj H2a H2b) => conj (conj H1a H2a) (conj H1b H2b) end) _ _).
exact (proj1 (interp_list_app _ _ _ _) H1).
exact (proj1 (interp_list_app _ _ _ _) H2).
intros ((H1a,H1b),(H2a,H2b)).
split.
exact (proj2 (interp_list_app true _ _ _) (conj H1a H2a)).
exact (proj2 (interp_list_app true _ _ _) (conj H1b H2b)).
split.
intros [H|H].
apply interp_list_app in H.
destruct H as [H|H].
left.
now left.
right.
now left.
apply interp_list_app in H.
destruct H as [H|H].
left.
now right.
right.
now right.
intros [[H|H]|[H|H]].
left.
apply interp_list_app.
now left.
right.
apply interp_list_app.
now left.
left.
apply interp_list_app.
now right.
right.
apply interp_list_app.
now right.
Qed.

Fixpoint flatten t :=
  match t with
  | Ttree cnj la lt =>
    let ft := fix ft lt :=
      match lt with
      | nil => (nil, nil)
      | t :: lt =>
        let '(la', lt') := ft lt in
        let t' := flatten t in
        match t' with
        | Ttree cnj' la lt =>
          match Bool.eqb cnj cnj', lt, la with
          | true, _, _ => (app la la', app lt lt')
          | _, nil, (a :: nil) => (cons a la', lt')
          | _, _, _ => (la', cons t lt')
          end
        end
      end in
    match la, lt with
    | nil, (t :: nil) => flatten t
    | _, _ =>
      let '(la', lt') := ft lt in
      Ttree cnj (app la la') lt'
    end
  end.

Theorem flatten_correct :
  forall rm t, interp_tree (flatten t) rm <-> interp_tree t rm.
Proof.
intros rm.
fix 1.
intros (cnj,la,lt).
set (ft := fix ft lt :=
      match lt with
      | nil => (nil, nil)
      | t :: lt =>
        let '(la', lt') := ft lt in
        let t' := flatten t in
        match t' with
        | Ttree cnj' la lt =>
          match Bool.eqb cnj cnj', lt, la with
          | true, _, _ => (app la la', app lt lt')
          | _, nil, (a :: nil) => (cons a la', lt')
          | _, _, _ => (la', cons t lt')
          end
        end
      end).
assert (interp_tree (let '(la',lt') := ft lt in Ttree cnj (app la la') lt') rm
  <-> interp_tree (Ttree cnj la lt) rm).
assert (interp_list_tree cnj lt rm <->
  let '(la', lt') := ft lt in interp_lists cnj la' lt' rm).
induction lt as [|t lt].
destruct cnj.
easy.
split.
intros [].
intros [[]|[]].
simpl.
clearbody ft.
destruct (ft lt) as (la'', lt'').
specialize (flatten_correct t).
destruct (flatten t) as (cnj',la',lt').
generalize (Bool.eqb_prop cnj cnj').
case Bool.eqb.
intros H.
rewrite <- H in flatten_correct by easy.
clear H.
destruct cnj.
split.
intros H.
apply interp_lists_app.
split.
apply (interp_tree_correct (Ttree true la' lt')).
apply flatten_correct.
exact (proj1 H).
apply IHlt.
exact (proj2 H).
intros H.
apply interp_lists_app in H.
split.
apply flatten_correct.
now apply interp_tree_correct.
now apply IHlt.
split.
intros [H|H].
apply interp_lists_app.
left.
apply (interp_tree_correct (Ttree false la' lt')).
now apply flatten_correct.
apply interp_lists_app.
right.
now apply IHlt.
intros H.
apply interp_lists_app in H.
destruct H as [H|H].
left.
apply flatten_correct.
now apply interp_tree_correct.
apply IHlt in H.
now right.
intros _.
assert (interp_list_tree cnj (t :: lt) rm <-> interp_lists cnj la'' (t :: lt'') rm).
destruct cnj as [|].
split.
intros (H1,H2).
split.
now apply IHlt.
split.
exact H1.
now apply IHlt.
intros (H1,(H2,H3)).
split.
exact H2.
apply IHlt.
now split.
split.
intros [H|H].
right.
now left.
destruct (proj1 IHlt) as [H'|H'].
easy.
now left.
right.
now right.
intros H.
destruct H as [H|[H|H]].
right.
apply (proj2 IHlt).
now left.
now left.
right.
apply (proj2 IHlt).
now right.
(* *)
destruct lt' as [|t' lt'] ; try easy.
destruct la' as [|a' [|a'' la']] ; try easy.
destruct cnj.
split.
intros (H1,H2).
split.
split.
now apply flatten_correct.
now apply IHlt.
now apply IHlt.
intros ((H1,H2),H3).
split.
now apply flatten_correct.
apply IHlt.
now split.
split.
intros [H'|H'].
left.
left.
now apply flatten_correct.
destruct (proj1 IHlt H') as [H''|H''].
left.
now right.
now right.
intros [[H'|H']|H'].
left.
now apply flatten_correct.
apply H.
now left.
apply H.
right.
now right.
(* *)
clearbody ft.
apply iff_sym.
destruct (ft lt) as (la', lt').
rewrite <- (app_nil_l lt').
destruct cnj as [|].
split.
intros H'.
apply interp_tree_correct in H'.
destruct H' as (H1,H2).
apply interp_tree_correct.
apply interp_lists_app.
split.
now split.
now apply H.
intros H'.
apply interp_tree_correct in H'.
apply interp_lists_app in H'.
apply interp_tree_correct.
split.
apply H'.
now apply H.
split.
intros H'.
apply interp_tree_correct in H'.
apply interp_tree_correct.
apply interp_lists_app.
destruct H' as [H'|H'].
left.
now left.
right.
now apply H.
intros H'.
apply interp_tree_correct in H'.
apply interp_tree_correct.
apply interp_lists_app in H'.
destruct H' as [[H'|[]]|H'].
now left.
right.
now apply H.
(* *)
change (flatten (Ttree cnj la lt)) with
  (match la, lt with
    | nil, (t :: nil) => flatten t
    | _, _ =>
      let '(la', lt') := ft lt in
      Ttree cnj (app la la') lt'
    end).
destruct la as [|a la].
destruct lt as [|t lt].
now clear flatten_correct.
destruct lt as [|t' lt].
simpl.
apply flatten_correct.
now clear flatten_correct.
now clear flatten_correct.
Qed.

Inductive atom_relation :=
  | ARimply
  | ARcontradict
  | ARunknown.

Definition subset (xi yi : FF) :=
  if Fle2 (lower yi) (lower xi) then Fle2 (upper xi) (upper yi) else false.

Definition empty_inter (xi yi : FF) :=
  if Flt2 (upper xi) (lower yi) then true else Flt2 (upper yi) (lower xi).

Definition compare xi yi (ypos:bool) :=
  if ypos then
    if subset xi yi then ARimply
    else if empty_inter xi yi then ARcontradict
    else ARunknown
  else
    if subset xi yi then ARcontradict
    else if empty_inter xi yi then ARimply
    else ARunknown.

Lemma compare_correct :
  forall xi yi ypos,
  forall x, BND x xi ->
  match compare xi yi ypos with
  | ARimply => if ypos then BND x yi else not (BND x yi)
  | ARcontradict => not (if ypos then BND x yi else not (BND x yi))
  | ARunknown => True
  end.
Proof.
intros (xl,xu) (yl,yu) ypos x ; unfold compare, subset, empty_inter, BND ; simpl.
intros (Hx1,Hx2).
generalize (Fle2_correct yl xl) (Fle2_correct xu yu) (Flt2_correct xu yl) (Flt2_correct yu xl).
case Fle2.
case Fle2.
intros H1 H2 _ _.
assert (yl <= x <= yu)%R.
split.
apply Rle_trans with (2 := Hx1).
now apply H1.
apply Rle_trans with (1 := Hx2).
now apply H2.
case ypos.
exact H.
intros H'.
now apply H'.
case Flt2.
intros H1 _ H2 _.
apply False_rec.
apply (Rlt_irrefl yl).
apply Rle_lt_trans with (1 := H1 eq_refl).
apply Rle_lt_trans with (1 := Hx1).
apply Rle_lt_trans with (1 := Hx2).
now apply H2.
case Flt2.
intros _ _ _ H.
assert (~(yl <= x <= yu)%R).
intros (_,Hy).
apply (Rlt_irrefl x).
apply Rle_lt_trans with (1 := Hy).
apply Rlt_le_trans with (2 := Hx1).
now apply H.
now case ypos.
intros _ _ _ _.
now case ypos.
case Flt2.
intros _ _ H _.
assert (~(yl <= x <= yu)%R).
intros (Hy,_).
apply (Rlt_irrefl x).
apply Rle_lt_trans with (1 := Hx2).
apply Rlt_le_trans with (2 := Hy).
now apply H.
now case ypos.
case Flt2.
intros _ _ _ H.
assert (~(yl <= x <= yu)%R).
intros (_,Hy).
apply (Rlt_irrefl x).
apply Rle_lt_trans with (1 := Hy).
apply Rlt_le_trans with (2 := Hx1).
now apply H.
now case ypos.
now case ypos.
Qed.

Definition weak_compare xi yi (ypos:bool) :=
  if ypos then
    if subset xi yi then ARimply
    else ARunknown
  else
    if subset xi yi then ARcontradict
    else ARunknown.

Lemma weak_compare_correct :
  forall xi yi ypos,
  forall x, BND x xi ->
  match weak_compare xi yi ypos with
  | ARimply => if ypos then BND x yi else False
  | ARcontradict => not (if ypos then True else not (BND x yi))
  | ARunknown => True
  end.
Proof.
intros xi yi ypos x Hx.
generalize (compare_correct xi yi ypos x Hx).
unfold compare, weak_compare.
now case ypos ; case subset.
Qed.

Definition relate (p : pos_atom) (q : atom) : atom_relation :=
  match p, q with
  | Abnd px pi, (Abnd qx qi, pos) =>
    if index_eq px qx then compare pi qi pos else ARunknown
  | Aabs px pi, (Aabs qx qi, pos) =>
    if index_eq px qx then if Fpos0 (lower qi) then compare pi qi pos else ARunknown else ARunknown
  | Arel px py pi, (Arel qx qy qi, pos) =>
    if index_eq px qx then if index_eq py qy then weak_compare pi qi pos else ARunknown else ARunknown
  | Afix px pc, (Afix qx qc, pos) =>
    if index_eq px qx then if Zle_bool qc pc then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | Aflt px pc, (Aflt qx qc, pos) =>
    if index_eq px qx then if Zle_bool (Zpos pc) (Zpos qc) then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | Anzr px, (Anzr qx, pos) =>
    if index_eq px qx then if pos then ARimply else ARcontradict else ARunknown
  | Aeql px py, (Aeql qx qy, pos) =>
    if index_eq px qx then if index_eq py qy then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | _, _ => ARunknown
  end.

Theorem relate_correct :
  forall p q rm,
  interp_pos_atom p rm ->
  match relate p q with
  | ARimply => interp_atom q rm
  | ARcontradict => not (interp_atom q rm)
  | ARunknown => True
  end.
Proof.
intros [px pi|px pi|px py pi|px pc|px pc|px|px py] ([qx qi|qx qi|qx qy qi|qx qc|qx qc|qx|qx qy],pos) rm Hp ; try exact I ; simpl.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (compare_correct pi qi pos _ Hp).
now case compare.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (Fpos0_correct (lower qi)).
case Fpos0 ; try easy.
intros H'.
specialize (H' eq_refl).
generalize (compare_correct pi qi pos _ (proj2 Hp)).
case compare ; try easy.
case pos ; intros H''.
now split.
contradict H''.
apply H''.
intros H''.
contradict H''.
destruct pos.
apply H''.
contradict H''.
now split.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
clear H.
generalize (index_eq_correct py qy).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
clear H.
destruct Hp as (e,(He,Hp)).
generalize (weak_compare_correct pi qi pos _ He).
case weak_compare ; try easy.
case pos ; intros H ; try easy.
exists e.
now split.
case pos ; intros H.
now contradict H.
contradict H.
contradict H.
exists e.
now split.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
clear H.
generalize (Zle_cases qc pc).
case (Zle_bool qc pc) ; try easy.
intros H.
destruct Hp as ((m,e),(Hm,He)).
case pos.
exists (Float2 m e).
split.
exact Hm.
now apply Zle_trans with (1 := H).
intros H'.
contradict H'.
exists (Float2 m e).
split.
exact Hm.
now apply Zle_trans with (1 := H).
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
clear H.
generalize (Zle_cases (Zpos pc) (Zpos qc)).
case Zle_bool ; try easy.
intros H.
destruct Hp as ((m,e),(Hm,He)).
case pos.
exists (Float2 m e).
split.
exact Hm.
apply Zlt_le_trans with (1 := He).
apply le_Z2R.
change (Z2R (Zpower radix2 (Zpos pc)) <= Z2R (Zpower radix2 (Zpos qc)))%R.
apply Z2R_le.
now apply Zpower_le.
intros H'.
contradict H'.
exists (Float2 m e).
split.
exact Hm.
apply Zlt_le_trans with (1 := He).
apply le_Z2R.
change (Z2R (Zpower radix2 (Zpos pc)) <= Z2R (Zpower radix2 (Zpos qc)))%R.
apply Z2R_le.
now apply Zpower_le.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
now case pos.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
clear H.
generalize (index_eq_correct py qy).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
clear H.
now case pos.
Qed.

Inductive truth_value {A : Type} :=
  | TVtrue
  | TVfalse
  | TVother : A -> truth_value.

Fixpoint simplify' t p :=
  match t with
  | Ttree cnj la lt =>
    let ft := fix ft lt :=
      match lt with
      | nil => if cnj then TVtrue else TVfalse
      | t :: lt =>
        match simplify' t p, cnj, ft lt with
        | TVtrue, true, lt => lt
        | TVtrue, false, _ => TVtrue
        | TVfalse, true, _ => TVfalse
        | TVfalse, false, lt => lt
        | TVother t, true, TVtrue => TVother (t :: nil)
        | TVother _, true, TVfalse => TVfalse
        | TVother t, true, TVother lt => TVother (t :: lt)
        | TVother _, false, TVtrue => TVtrue
        | TVother t, false, TVfalse => TVother (t :: nil)
        | TVother t, false, TVother lt => TVother (t :: lt)
        end
      end in
    let fa := fix fa la :=
      match la with
      | nil => if cnj then TVtrue else TVfalse
      | a :: la =>
        match relate p a, cnj, fa la with
        | ARimply, true, la => la
        | ARimply, false, _ => TVtrue
        | ARcontradict, true, _ => TVfalse
        | ARcontradict, false, la => la
        | ARunknown, true, TVtrue => TVother (a :: nil)
        | ARunknown, true, TVfalse => TVfalse
        | ARunknown, true, TVother la => TVother (a :: la)
        | ARunknown, false, TVtrue => TVtrue
        | ARunknown, false, TVfalse => TVother (a :: nil)
        | ARunknown, false, TVother la => TVother (a :: la)
        end
      end in
    match fa la, cnj, ft lt with
    | TVtrue, true, TVtrue => TVtrue
    | TVtrue, true, TVfalse => TVfalse
    | TVtrue, true, TVother lt => TVother (flatten (Ttree cnj nil lt))
    | TVtrue, false, _ => TVtrue
    | TVfalse, true, _ => TVfalse
    | TVfalse, false, TVtrue => TVtrue
    | TVfalse, false, TVfalse => TVfalse
    | TVfalse, false, TVother lt => TVother (flatten (Ttree cnj nil lt))
    | TVother la, true, TVtrue => TVother (Ttree cnj la nil)
    | TVother _, true, TVfalse => TVfalse
    | TVother la, true, TVother lt => TVother (flatten (Ttree cnj la lt))
    | TVother _, false, TVtrue => TVtrue
    | TVother la, false, TVfalse => TVother (flatten (Ttree cnj la nil))
    | TVother la, false, TVother lt => TVother (flatten (Ttree cnj la lt))
    end
  end.

Lemma iff_True :
  forall P : Prop, P <-> (P <-> True).
Proof.
split.
now split.
intros (_,H).
now apply H.
Qed.

Lemma iff_False :
  forall P : Prop, not P <-> (P <-> False).
Proof.
split.
now split.
now intros (H,_).
Qed.

Theorem simplify'_correct :
  forall t p rm,
  interp_pos_atom p rm ->
  (interp_tree t rm <->
  match simplify' t p with
  | TVtrue => True
  | TVfalse => False
  | TVother t => interp_tree t rm
  end).
Proof.
intros t p rm Hp.
revert t.
fix 1.
intros (cnj,la,lt).
set (ft := fix ft lt :=
      match lt with
      | nil => if cnj then TVtrue else TVfalse
      | t :: lt =>
        match simplify' t p, cnj, ft lt with
        | TVtrue, true, lt => lt
        | TVtrue, false, _ => TVtrue
        | TVfalse, true, _ => TVfalse
        | TVfalse, false, lt => lt
        | TVother t, true, TVtrue => TVother (t :: nil)
        | TVother _, true, TVfalse => TVfalse
        | TVother t, true, TVother lt => TVother (t :: lt)
        | TVother _, false, TVtrue => TVtrue
        | TVother t, false, TVfalse => TVother (t :: nil)
        | TVother t, false, TVother lt => TVother (t :: lt)
        end
      end).
assert (Ht: interp_list_tree cnj lt rm <->
  match ft lt with
  | TVtrue => True
  | TVfalse => False
  | TVother lt => interp_list_tree cnj lt rm
  end).
induction lt as [|t lt] ; simpl ; clearbody ft.
now destruct cnj.
generalize (simplify'_correct t).
clear simplify'_correct.
destruct (simplify' t p) as [| |t'].
intros (_,H).
specialize (H I).
destruct (ft lt) as [| |lt'].
apply <- iff_True in IHlt.
replace (if cnj then @TVtrue (list tree) else @TVtrue (list tree)) with (@TVtrue (list tree)) by now case cnj.
apply -> iff_True.
destruct cnj.
now split.
now left.
apply <- iff_False in IHlt.
destruct cnj.
apply -> iff_False.
now intros (_,H').
apply -> iff_True.
now left.
destruct cnj.
apply iff_trans with (2 := IHlt).
split.
now intros (_,H').
intros H'.
now split.
apply -> iff_True.
now left.
intros H.
apply <- iff_False in H.
destruct (ft lt) as [| |lt'].
apply <- iff_True in IHlt.
destruct cnj.
apply -> iff_False.
now intros (H',_).
apply -> iff_True.
now right.
apply <- iff_False in IHlt.
replace (if cnj then @TVfalse (list tree) else @TVfalse (list tree)) with (@TVfalse (list tree)) by now case cnj.
apply -> iff_False.
destruct cnj.
now intros (_,H').
now intros [H'|H'].
destruct cnj.
apply -> iff_False.
now intros (H',_).
apply iff_trans with (2 := IHlt).
split.
now intros [H'|H'].
intros H'.
now right.
intros H.
destruct (ft lt) as [| |lt'].
apply <- iff_True in IHlt.
destruct cnj.
now split ; intros (H1,H2) ; split ; try apply H.
apply -> iff_True.
now right.
apply <- iff_False in IHlt.
destruct cnj.
apply -> iff_False.
now intros (_,H').
now split ; intros [H'|H'] ; try (left ; apply H).
destruct cnj.
now split ; intros (H1,H2) ; split ; try apply H ; try apply IHlt.
split ; intros [H'|H'].
left.
now apply H.
right.
now apply IHlt.
left.
now apply H.
right.
now apply IHlt.
(* *)
clear simplify'_correct.
set (fa := fix fa la :=
      match la with
      | nil => if cnj then TVtrue else TVfalse
      | a :: la =>
        match relate p a, cnj, fa la with
        | ARimply, true, la => la
        | ARimply, false, _ => TVtrue
        | ARcontradict, true, _ => TVfalse
        | ARcontradict, false, la => la
        | ARunknown, true, TVtrue => TVother (a :: nil)
        | ARunknown, true, TVfalse => TVfalse
        | ARunknown, true, TVother la => TVother (a :: la)
        | ARunknown, false, TVtrue => TVtrue
        | ARunknown, false, TVfalse => TVother (a :: nil)
        | ARunknown, false, TVother la => TVother (a :: la)
        end
      end).
assert (Ha: interp_list_atom cnj la rm <->
  match fa la with
  | TVtrue => True
  | TVfalse => False
  | TVother la => interp_list_atom cnj la rm
  end).
clearbody ft.
clear Ht.
induction la as [|a la] ; simpl ; clearbody fa.
now destruct cnj.
generalize (relate_correct p a rm Hp).
destruct (relate p a) as [| |].
intros H.
destruct (fa la) as [| |la'].
apply <- iff_True in IHla.
replace (if cnj then @TVtrue (list atom) else @TVtrue (list atom)) with (@TVtrue (list atom)) by now case cnj.
apply -> iff_True.
destruct cnj.
now split.
now left.
apply <- iff_False in IHla.
destruct cnj.
apply -> iff_False.
now intros (_,H').
apply -> iff_True.
now left.
destruct cnj.
apply iff_trans with (2 := IHla).
split.
now intros (_,H').
intros H'.
now split.
apply -> iff_True.
now left.
intros H.
destruct (fa la) as [| |la'].
apply <- iff_True in IHla.
destruct cnj.
apply -> iff_False.
now intros (H',_).
apply -> iff_True.
now right.
apply <- iff_False in IHla.
replace (if cnj then @TVfalse (list atom) else @TVfalse (list atom)) with (@TVfalse (list atom)) by now case cnj.
apply -> iff_False.
destruct cnj.
now intros (_,H').
now intros [H'|H'].
destruct cnj.
apply -> iff_False.
now intros (H',_).
apply iff_trans with (2 := IHla).
split.
now intros [H'|H'].
intros H'.
now right.
intros _.
destruct (fa la) as [| |la'].
apply <- iff_True in IHla.
destruct cnj.
now split ; intros (H1,H2) ; split.
apply -> iff_True.
now right.
apply <- iff_False in IHla.
destruct cnj.
apply -> iff_False.
now intros (_,H').
now split ; intros [H|H] ; try left.
destruct cnj.
now split ; intros (H1,H2) ; split ; try apply H ; try apply IHla.
split ; intros [H'|H'].
now left.
right.
now apply IHla.
now left.
right.
now apply IHla.
(* *)
change (simplify' (Ttree cnj la lt) p) with
    match fa la, cnj, ft lt with
    | TVtrue, true, TVtrue => TVtrue
    | TVtrue, true, TVfalse => TVfalse
    | TVtrue, true, TVother lt => TVother (flatten (Ttree cnj nil lt))
    | TVtrue, false, _ => TVtrue
    | TVfalse, true, _ => TVfalse
    | TVfalse, false, TVtrue => TVtrue
    | TVfalse, false, TVfalse => TVfalse
    | TVfalse, false, TVother lt => TVother (flatten (Ttree cnj nil lt))
    | TVother la, true, TVtrue => TVother (Ttree cnj la nil)
    | TVother _, true, TVfalse => TVfalse
    | TVother la, true, TVother lt => TVother (flatten (Ttree cnj la lt))
    | TVother _, false, TVtrue => TVtrue
    | TVother la, false, TVfalse => TVother (flatten (Ttree cnj la nil))
    | TVother la, false, TVother lt => TVother (flatten (Ttree cnj la lt))
    end.
clearbody ft fa.
rewrite interp_tree_correct.
destruct (fa la) as [| |la'].
apply <- iff_True in Ha.
destruct (ft lt) as [| |lt'].
apply <- iff_True in Ht.
replace (if cnj then @TVtrue tree else @TVtrue tree) with (@TVtrue tree) by now case cnj.
apply -> iff_True.
destruct cnj.
now split.
now left.
apply <- iff_False in Ht.
destruct cnj.
apply -> iff_False.
now intros (_,H').
apply -> iff_True.
now left.
destruct cnj.
rewrite flatten_correct.
rewrite interp_tree_correct.
now split ; intros (H1,H2) ; split ; try apply Ht.
apply -> iff_True.
now left.
apply <- iff_False in Ha.
destruct (ft lt) as [| |lt'].
apply <- iff_True in Ht.
destruct cnj.
apply -> iff_False.
now intros (H',_).
apply -> iff_True.
now right.
apply <- iff_False in Ht.
replace (if cnj then @TVfalse tree else @TVfalse tree) with (@TVfalse tree) by now case cnj.
apply -> iff_False.
destruct cnj.
now intros (H',_).
now intros [H'|H'].
destruct cnj.
apply -> iff_False.
now intros (H',_).
rewrite flatten_correct.
rewrite interp_tree_correct.
now split ; intros [H'|H'] ; try (right ; apply Ht).
destruct (ft lt) as [| |lt'].
apply <- iff_True in Ht.
destruct cnj.
rewrite interp_tree_correct.
now split ; intros (H1,H2) ; split ; try apply Ha.
apply -> iff_True.
now right.
apply <- iff_False in Ht.
destruct cnj.
apply -> iff_False.
now intros (_,H').
rewrite flatten_correct.
rewrite interp_tree_correct.
now split ; intros [H'|H'] ; try (left ; apply Ha).
destruct cnj.
rewrite flatten_correct.
rewrite interp_tree_correct.
now split ; intros (H1,H2) ; split ; try apply Ha ; try apply Ht.
rewrite flatten_correct.
rewrite interp_tree_correct.
split ; intros [H'|H'].
left.
now apply Ha.
right.
now apply Ht.
left.
now apply Ha.
right.
now apply Ht.
Qed.

Theorem simplify :
  forall t p rm,
  interp_pos_atom p rm ->
  interp_tree t rm ->
  match simplify' t p with
  | TVtrue => True
  | TVfalse => False
  | TVother t => interp_tree t rm
  end.
Proof.
intros t p rm Hp.
now apply simplify'_correct.
Qed.
