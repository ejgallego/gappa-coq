FILES = \
	Gappa_common.v \
	Gappa_decimal.v \
	Gappa_definitions.v \
	Gappa_dyadic.v \
	Gappa_fixed.v \
	Gappa_float.v \
	Gappa_integer.v \
	Gappa_library.v \
	Gappa_obfuscate.v \
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
	Gappa_tactic_legacy.v \
	Gappa_tactic_plugin.v \
	Gappa_user.v

data_DATA = $(FILES:=o) $(TACTIC_TARGETS) Gappa_tactic.vo
EXTRA_DIST = $(FILES) gappatac.ml
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob) \
	gappatac.cmi gappatac.cmo gappatac.cmx gappatac.cmxs gappatac.o \
	Gappa_tactic.v Gappa_tactic.vo Gappa_tactic.glob

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I . $< > $@

SUFFIXES = .v .vo .vd

COQSUBTREES = kernel lib interp parsing proofs pretyping tactics library

Gappa_tactic_plugin.vo: Gappa_tactic_plugin.v $(TACTIC_TARGETS)
	@echo COQC $<
	@$(COQC) $(TACTIC_PARAM) $(COQRFLAG) -dont-load-proofs $<

Gappa_tactic.vo: Gappa_tactic.v
	@echo COQC $<
	@$(COQC) $(TACTIC_PARAM) $(COQRFLAG) -dont-load-proofs $<

Gappa_tactic.vd: Gappa_tactic.v

Gappa_tactic.v: $(TACTIC_DEFAULT)
	@echo GENR $@
	@if test "$(TACTIC_DEFAULT)" = "Gappa_tactic_plugin.v"; then \
	  echo 'Require Export Gappa_tactic_plugin.' > $@; \
	else \
	  cp $< $@; \
	fi

gappatac.cmo: gappatac.ml
	@echo OCAMLC $<
	@$(OCAMLC) -rectypes $(COQSUBTREES:%=-I $(COQLIBS)/%) $< -c -o $@

gappatac.cmxs: gappatac.ml
	@echo OCAMLOPT $<
	@$(OCAMLOPT) -shared -rectypes $(COQSUBTREES:%=-I $(COQLIBS)/%) $< -o $@

-include $(FILES:=d) Gappa_tactic.vd
