Add LoadPath "/usr/src/coq/Float".
Require Export IA_float.

Section IA_754s.

Let precision := 24.
Let precisionMoreThanOne : 1 < precision.
unfold precision. auto with zarith.
Qed.
Let bExp := 149.

Definition f754s := cFloat precision bExp.
Definition Good_f754s := Fcanonic radix (bound precision bExp).
Definition F754s (f : float) (p : Good_f754s f) := CFloat precision bExp f p.

Definition I754s := makepairF precision bExp.
Definition I754s_in := IintF precision bExp.
Definition I754s_add_bnd := add_bound precision precisionMoreThanOne bExp.
Definition I754s_sub_bnd := sub_bound precision precisionMoreThanOne bExp.

Definition add_754s := cFloat_add precision bExp.
Definition sub_754s := cFloat_sub precision bExp.
Definition mul_754s := cFloat_mul precision bExp.
Definition div_754s := cFloat_div precision bExp.

Lemma Normal_f754s: forall P, (Lt = Lt /\ (Lt = Gt -> False)) /\ (Eq = Gt -> False) \/ P.
intro P. apply or_introl. repeat split; discriminate. Qed.
Lemma Subnormal_f754s: forall P, P \/ (Lt = Lt /\ (Eq = Gt -> False)) /\ (-149)%Z = (-149)%Z /\ Lt = Lt.
intro P. apply or_intror. repeat split; discriminate. Qed.

End IA_754s.
