FILES = \
	Gappa_common.v \
	Gappa_decimal.v \
	Gappa_definitions.v \
	Gappa_dyadic.v \
	Gappa_fixed.v \
	Gappa_float.v \
	Gappa_library.v \
	Gappa_pred_abs.v \
	Gappa_pred_bnd.v \
	Gappa_pred_fixflt.v \
	Gappa_pred_nzr.v \
	Gappa_pred_rel.v \
	Gappa_proxy.v \
	Gappa_real.v \
	Gappa_rewriting.v \
	Gappa_round_aux.v \
	Gappa_round_def.v \
	Gappa_round.v

data_DATA = $(FILES:=o)
EXTRA_DIST = autogen.sh $(FILES)
CLEANFILES = $(FILES:=o)

Gappa_common.vo: Gappa_common.v Gappa_real.vo Gappa_definitions.vo Gappa_dyadic.vo
Gappa_decimal.vo: Gappa_decimal.v Gappa_common.vo
Gappa_definitions.vo: Gappa_definitions.v
Gappa_dyadic.vo: Gappa_dyadic.v Gappa_definitions.vo
Gappa_fixed.vo: Gappa_fixed.v Gappa_definitions.vo Gappa_dyadic.vo Gappa_pred_bnd.vo Gappa_round_def.vo Gappa_round_aux.vo Gappa_round.vo
Gappa_float.vo: Gappa_float.v Gappa_definitions.vo Gappa_dyadic.vo Gappa_pred_bnd.vo Gappa_round_def.vo Gappa_round_aux.vo Gappa_round.vo
Gappa_library.vo: Gappa_library.v Gappa_definitions.vo Gappa_pred_bnd.vo Gappa_pred_abs.vo Gappa_pred_fixflt.vo Gappa_pred_nzr.vo Gappa_pred_rel.vo Gappa_rewriting.vo Gappa_round_def.vo Gappa_fixed.vo Gappa_float.vo Gappa_proxy.vo
Gappa_pred_abs.vo: Gappa_pred_abs.v Gappa_common.vo Gappa_pred_nzr.vo
Gappa_pred_bnd.vo: Gappa_pred_bnd.v Gappa_common.vo Gappa_decimal.vo
Gappa_pred_fixflt.vo: Gappa_pred_fixflt.v Gappa_common.vo Gappa_round_aux.vo
Gappa_pred_nzr.vo: Gappa_pred_nzr.v Gappa_common.vo
Gappa_pred_rel.vo: Gappa_pred_rel.v Gappa_common.vo Gappa_pred_bnd.vo
Gappa_proxy.vo: Gappa_proxy.v Gappa_common.vo
Gappa_real.vo: Gappa_real.v
Gappa_rewriting.vo: Gappa_rewriting.v Gappa_common.vo
Gappa_round_aux.vo: Gappa_round_aux.v Gappa_definitions.vo Gappa_dyadic.vo
Gappa_round_def.vo: Gappa_round_def.v
Gappa_round.vo: Gappa_round.v Gappa_definitions.vo Gappa_dyadic.vo Gappa_round_def.vo Gappa_round_aux.vo

%.vo: %.v
	$(COQC) $<
