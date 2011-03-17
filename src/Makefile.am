FILES = \
	Gappa_common.v \
	Gappa_decimal.v \
	Gappa_definitions.v \
	Gappa_dyadic.v \
	Gappa_fixed.v \
	Gappa_float.v \
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
	Gappa_tactic.v \
	Gappa_user.v

data_DATA = $(FILES:=o) $(TACTIC_TARGETS)
EXTRA_DIST = $(FILES) gappatac.ml
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob) \
	gappatac.cmi gappatac.cmo gappatac.cmx gappatac.cmxs gappatac.o

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I . $< > $@

SUFFIXES = .v .vo .vd

COQSUBTREES = kernel lib interp parsing proofs pretyping tactics library toplevel

PP = -pp "$(CAMLP4)o $(COQLIBS)/parsing/grammar.cma"

Gappa_tactic.vo: Gappa_tactic.v $(TACTIC_TARGETS)
	@echo COQC $<
	@$(COQC) $(TACTIC_PARAM) $(COQRFLAG) -dont-load-proofs $<

gappatac.cmo: gappatac.ml
	@echo OCAMLC $<
	@$(OCAMLC) $(PP) -rectypes $(COQSUBTREES:%=-I $(COQLIBS)/%) $< -c -o $@

gappatac.cmxs: gappatac.ml
	@echo OCAMLOPT $<
	@$(OCAMLOPT) $(PP) -shared -rectypes $(COQSUBTREES:%=-I $(COQLIBS)/%) $< -o $@

-include $(FILES:=d) Gappa_tactic.vd
