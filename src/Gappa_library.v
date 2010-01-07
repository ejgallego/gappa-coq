Require Export Rdefinitions.
Require Export Rbasic_fun.
Require Export R_sqrt.
Require Export Bool.
Require Export Gappa_definitions.
Require Export Gappa_pred_bnd.
Require Export Gappa_pred_abs.
Require Export Gappa_pred_fixflt.
Require Export Gappa_pred_nzr.
Require Export Gappa_pred_rel.
Require Export Gappa_rewriting.
Require Export Gappa_round_def.
Require Export Gappa_fixed.
Require Export Gappa_float.
Require Export Gappa_user.
Require Export Gappa_proxy.

Ltac finalize := vm_cast_no_check (refl_equal true).
Ltac next_interval t h :=
 apply t with (1 := h) ; [ finalize |
 clear h ; intro h ; simpl in h ; generalize h ; clear h ].
