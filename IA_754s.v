Add LoadPath "/usr/src/coq/Float".
Require Export IA_float.

Section IA_754s.

Let precision := 24.
Let precisionMoreThanOne : 1 < precision.
unfold precision. auto with zarith.
Qed.
Let bExp := 149.

Definition I754s := FF precision bExp.
Definition I754s_add_bound := add_bound precision precisionMoreThanOne bExp.

Definition f754s := cFloat precision bExp.
Definition Good_f754s := Fcanonic radix (bound precision bExp).
Definition F754s (f : float) (p : Good_f754s f) := CFloat precision bExp f p.
Definition add_754s := cFloat_add precision bExp.
Definition sub_754s := cFloat_sub precision bExp.
Definition mul_754s := cFloat_mul precision bExp.
Definition div_754s := cFloat_div precision bExp.

End IA_754s.
