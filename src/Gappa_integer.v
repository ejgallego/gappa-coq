Require Export Fcore_Raux.

Section Gappa_integer.

Definition F2R radix m e :=
  match e with
  | Zpos p => Z2R (m * Zpower_pos (Zpos radix) p)
  | Z0 => Z2R m
  | Zneg p => (Z2R m / Z2R (Zpower_pos (Zpos radix) p))%R
  end.

Lemma F2R_split :
  forall radix m e,
  (F2R radix m e = Z2R m * powerRZ (P2R radix) e)%R.
intros.
unfold F2R.
destruct e.
apply sym_eq.
apply Rmult_1_r.
rewrite mult_Z2R.
rewrite Zpower_pos_powerRZ.
apply refl_equal.
rewrite Zpower_pos_powerRZ.
apply refl_equal.
Qed.

End Gappa_integer.