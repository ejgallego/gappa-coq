FILES = \
	Gappa_common.v \
	Gappa_decimal.v \
	Gappa_definitions.v \
	Gappa_dyadic.v \
	Gappa_library.v \
	Gappa_pred_abs.v \
	Gappa_pred_bnd.v \
	Gappa_pred_fixflt.v \
	Gappa_real.v \
	Gappa_rewriting.v

data_DATA = $(FILES:=o)
EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o)

Gappa_common.vo: Gappa_common.v Gappa_real.vo Gappa_definitions.vo Gappa_dyadic.vo
Gappa_decimal.vo: Gappa_decimal.v Gappa_common.vo
Gappa_definitions.vo: Gappa_definitions.v
Gappa_dyadic.vo: Gappa_dyadic.v Gappa_definitions.vo
Gappa_library.vo: Gappa_library.v Gappa_definitions.vo Gappa_pred_bnd.vo Gappa_pred_abs.vo Gappa_pred_fixflt.vo Gappa_rewriting.vo
Gappa_pred_abs.vo: Gappa_pred_abs.v Gappa_common.vo
Gappa_pred_bnd.vo: Gappa_pred_bnd.v Gappa_common.vo Gappa_decimal.vo
Gappa_pred_fixflt.vo: Gappa_pred_fixflt.v Gappa_common.vo
Gappa_real.vo: Gappa_real.v
Gappa_rewriting.vo: Gappa_rewriting.v Gappa_common.vo

%.vo: %.v
	@COQC@ $<
