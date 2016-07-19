Require Export Rdefinitions.
Require Export Rbasic_fun.
Require Export R_sqrt.
Require Export Bool.
Require Export Gappa_definitions.
Require Export Gappa_tree.
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

Ltac finalize := vm_cast_no_check (refl_equal true).
