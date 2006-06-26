Require Export Rdefinitions.
Require Export Gappa_common.
Require Export Gappa_pred_bnd.
Require Export Gappa_pred_abs.
Require Export Gappa_pred_fixflt.
Require Export Gappa_rewriting.

Ltac finalize := exact (refl_equal true).
Ltac next_interval t h :=
 apply t with (1 := h) ; [ finalize |
 clear h ; intro h ; simpl in h ; generalize h ; clear h ].
