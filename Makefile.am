FILES = \
	Gappa_common.v \
	Gappa_decimal.v \
	Gappa_definitions.v \
	Gappa_dyadic.v \
	Gappa_fixed.v \
	Gappa_float.v \
	Gappa_integer.v \
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
	Gappa_round.v \
	Gappa_tactic.v \
	Gappa_user.v

data_DATA = $(FILES:=o)
EXTRA_DIST = autogen.sh $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob)

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I . $< > $@

SUFFIXES = .v .vo .vd

-include $(FILES:=d)
