Require Import Reals List Bool.
Require Import Gappa_common.

Notation index := nat.
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
  | Aleq : index -> float2 -> pos_atom
  | Ageq : index -> float2 -> pos_atom
  | Aabs : index -> FF -> pos_atom
  | Arel : index -> index -> FF -> pos_atom
  | Afix : index -> Z -> pos_atom
  | Aflt : index -> positive -> pos_atom
  | Anzr : index -> pos_atom
  | Aeql : index -> index -> pos_atom.

Definition interp_pos_atom a rm :=
  match a with
  | Abnd x xi => BND (get rm x) xi
  | Aleq x xu => Rle (get rm x) xu
  | Ageq x xl => Rle xl (get rm x)
  | Aabs x xi => ABS (get rm x) xi
  | Arel x y xi => REL (get rm x) (get rm y) xi
  | Afix x xc => FIX (get rm x) xc
  | Aflt x xc => FLT (get rm x) xc
  | Anzr x => NZR (get rm x)
  | Aeql x y => get rm x = get rm y
  end.

Definition interp_atom a (pos : bool) rm :=
  let p := interp_pos_atom a rm in if pos then p else not p.

Inductive tree :=
  | Ttrue
  | Tfalse
  | Ttree : bool -> tree -> tree -> tree
  | Tatom : bool -> pos_atom -> tree.

Fixpoint interp_tree t rm :=
  match t with
  | Ttrue => True
  | Tfalse => False
  | Ttree cnj l r =>
    (if cnj then and else or) (interp_tree l rm) (interp_tree r rm)
  | Tatom pos a => interp_atom a pos rm
  end.

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

Definition relate (p : pos_atom) (q : pos_atom) (pos : bool) : atom_relation :=
  match p, q with
  | Abnd px pi, Abnd qx qi =>
    if index_eq px qx then compare pi qi pos else ARunknown
  | Abnd px pi, Aleq qx qu =>
    if index_eq px qx then if Fle2 (upper pi) qu then if pos then ARimply else ARcontradict else if Flt2 qu (lower pi) then if pos then ARcontradict else ARimply else ARunknown else ARunknown
  | Abnd px pi, Ageq qx ql =>
    if index_eq px qx then if Fle2 ql (lower pi) then if pos then ARimply else ARcontradict else if Flt2 (upper pi) ql then if pos then ARcontradict else ARimply else ARunknown else ARunknown
  | Aabs px pi, Aabs qx qi =>
    if index_eq px qx then if Fpos0 (lower qi) then compare pi qi pos else ARunknown else ARunknown
  | Arel px py pi, Arel qx qy qi =>
    if index_eq px qx then if index_eq py qy then weak_compare pi qi pos else ARunknown else ARunknown
  | Afix px pc, Afix qx qc =>
    if index_eq px qx then if Zle_bool qc pc then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | Aflt px pc, Aflt qx qc =>
    if index_eq px qx then if Zle_bool (Zpos pc) (Zpos qc) then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | Anzr px, Anzr qx =>
    if index_eq px qx then if pos then ARimply else ARcontradict else ARunknown
  | Aeql px py, Aeql qx qy =>
    if index_eq px qx then if index_eq py qy then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | Aleq px pu, Aleq qx qu =>
    if index_eq px qx then if Fle2 pu qu then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | Aleq px pu, Ageq qx ql =>
    if index_eq px qx then if Flt2 pu ql then if pos then ARcontradict else ARimply else ARunknown else ARunknown
  | Ageq px pl, Aleq qx qu =>
    if index_eq px qx then if Flt2 qu pl then if pos then ARcontradict else ARimply else ARunknown else ARunknown
  | Ageq px pl, Ageq qx ql =>
    if index_eq px qx then if Fle2 ql pl then if pos then ARimply else ARcontradict else ARunknown else ARunknown
  | _, _ => ARunknown
  end.

Theorem relate_correct :
  forall p q pos rm,
  interp_pos_atom p rm ->
  match relate p q pos with
  | ARimply => interp_atom q pos rm
  | ARcontradict => not (interp_atom q pos rm)
  | ARunknown => True
  end.
Proof.
unfold interp_atom.
intros [px pi|px pu|px pl|px pi|px py pi|px pc|px pc|px|px py] [qx qi|qx qu|qx ql|qx qi|qx qy qi|qx qc|qx qc|qx|qx qy] pos rm Hp ; try exact I ; simpl.
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
generalize (Fle2_correct (upper pi) qu).
case Fle2.
intros H'.
assert (Rle (get rm qx) qu).
apply Rle_trans with (1 := proj2 Hp).
now apply H'.
now case pos.
intros _.
generalize (Flt2_correct qu (lower pi)).
case Flt2 ; try easy.
intros H'.
assert (not (Rle (get rm qx) qu)).
intros H''.
apply Rlt_not_le with (1 := H' eq_refl).
now apply Rle_trans with (1 := proj1 Hp).
now case pos.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (Fle2_correct ql (lower pi)).
case Fle2.
intros H'.
assert (Rle ql (get rm qx)).
apply Rle_trans with (2 := proj1 Hp).
now apply H'.
now case pos.
intros _.
generalize (Flt2_correct (upper pi) ql).
case Flt2 ; try easy.
intros H'.
assert (not (Rle ql (get rm qx))).
intros H''.
apply Rlt_not_le with (1 := H' eq_refl).
now apply Rle_trans with (2 := proj2 Hp).
now case pos.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (Fle2_correct pu qu).
case Fle2 ; try easy.
intros H'.
assert (Rle (get rm qx) qu).
apply Rle_trans with (1 := Hp).
now apply H'.
now case pos.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (Flt2_correct pu ql).
case Flt2 ; try easy.
intros H'.
assert (not (Rle ql (get rm qx))).
apply Rlt_not_le.
apply Rle_lt_trans with (1 := Hp).
now apply H'.
now case pos.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (Flt2_correct qu pl).
case Flt2 ; try easy.
intros H'.
assert (not (Rle (get rm qx) qu)).
apply Rlt_not_le.
apply Rlt_le_trans with (2 := Hp).
now apply H'.
now case pos.
(* *)
generalize (index_eq_correct px qx).
case index_eq ; try easy.
intros H.
rewrite H in Hp by easy.
generalize (Fle2_correct ql pl).
case Fle2 ; try easy.
intros H'.
assert (Rle ql (get rm qx)).
apply Rle_trans with (2 := Hp).
now apply H'.
now case pos.
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

Fixpoint simplify' t p :=
  match t with
  | Ttrue => Ttrue
  | Tfalse => Tfalse
  | Ttree cnj l r =>
    match simplify' l p, cnj, simplify' r p with
    | Ttrue, true, r => r
    | Ttrue, false, _ => Ttrue
    | Tfalse, true, _ => Tfalse
    | Tfalse, false, r => r
    | l, true, Ttrue => l
    | _, true, Tfalse => Tfalse
    | l, true, r => Ttree true l r
    | _, false, Ttrue => Ttrue
    | l, false, Tfalse => l
    | l, false, r => Ttree false l r
    end
  | Tatom pos a =>
    match relate p a pos with
    | ARimply => Ttrue
    | ARcontradict => Tfalse
    | ARunknown => t
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
  (interp_tree t rm <-> interp_tree (simplify' t p) rm).
Proof.
intros t p rm Hp.
induction t as [| |cnj l Hl r Hr|a pos] ; try easy.
simpl.
destruct (simplify' l p) as [| |cnj' l' r'|a' pos'].
simpl in Hl.
apply <- iff_True in Hl.
case cnj.
intuition.
apply -> iff_True.
now left.
apply <- iff_False in Hl.
case cnj.
apply -> iff_False.
now intros (H,_).
intuition.
destruct (simplify' r p) as [| |cnj'' l'' r''|a'' pos''].
apply <- iff_True in Hr.
case cnj.
intuition.
apply -> iff_True.
now right.
apply <- iff_False in Hr.
case cnj.
apply -> iff_False.
now intros (_,H).
intuition.
replace (interp_tree (if cnj
   then Ttree true (Ttree cnj' l' r') (Ttree cnj'' l'' r'')
   else Ttree false (Ttree cnj' l' r') (Ttree cnj'' l'' r'')) rm) with
  ((if cnj then and else or) (interp_tree (Ttree cnj' l' r') rm) (interp_tree (Ttree cnj'' l'' r'') rm))
  by now case cnj.
case cnj ; intuition.
replace (interp_tree (if cnj
   then Ttree true (Ttree cnj' l' r') (Tatom a'' pos'')
   else Ttree false (Ttree cnj' l' r') (Tatom a'' pos'')) rm) with
  ((if cnj then and else or) (interp_tree (Ttree cnj' l' r') rm) (interp_tree (Tatom a'' pos'') rm))
  by now case cnj.
case cnj ; intuition.
destruct (simplify' r p) as [| |cnj'' l'' r''|a'' pos''].
apply <- iff_True in Hr.
case cnj.
intuition.
apply -> iff_True.
now right.
apply <- iff_False in Hr.
case cnj.
apply -> iff_False.
now intros (_,H).
intuition.
replace (interp_tree (if cnj
   then Ttree true (Tatom a' pos') (Ttree cnj'' l'' r'')
   else Ttree false (Tatom a' pos') (Ttree cnj'' l'' r'')) rm) with
  ((if cnj then and else or) (interp_tree (Tatom a' pos') rm) (interp_tree (Ttree cnj'' l'' r'') rm))
  by now case cnj.
case cnj ; intuition.
replace (interp_tree (if cnj
   then Ttree true (Tatom a' pos') (Tatom a'' pos'')
   else Ttree false (Tatom a' pos') (Tatom a'' pos'')) rm) with
  ((if cnj then and else or) (interp_tree (Tatom a' pos') rm) (interp_tree (Tatom a'' pos'') rm))
  by now case cnj.
case cnj ; intuition.
(* *)
simpl.
generalize (relate_correct p pos a rm Hp).
case relate ; intros H.
now apply -> iff_True.
now apply -> iff_False.
easy.
Qed.

Scheme Equality for positive.
Scheme Equality for Z.
Scheme Equality for nat.
Scheme Equality for float2.
Scheme Equality for FF.
Scheme Equality for pos_atom.
Scheme Equality for tree.

Theorem simplify :
  forall t t' p rm,
  interp_pos_atom p rm ->
  interp_tree t rm ->
  tree_beq (simplify' t p) t' = true ->
  interp_tree t' rm.
Proof.
intros t t' p rm Hp Ht Hs.
rewrite <- (internal_tree_dec_bl _ _ Hs).
generalize (proj1 (simplify'_correct t p rm Hp)).
intuition.
Qed.
