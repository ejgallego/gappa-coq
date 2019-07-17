Version 1.4.2
-------------

- ensured compatibility from Coq 8.8 to 8.10

Version 1.4.1
-------------

- ensured compatibility from Coq 8.7 to 8.9

Version 1.4.0
-------------

- moved to Flocq 3.0 (incompatible with Coq < 8.7)

Version 1.3.4
-------------

- fixed some integer variables being recognized as constant with Coq 8.7
- ensured compatibility from Coq 8.4 to 8.8

Version 1.3.3
-------------

- fixed compilation with Coq 8.7

Version 1.3.2
-------------

- fixed compilation with Coq 8.6
- proved `div_firs`

Version 1.3.1
-------------

- ensured compatibility from Coq 8.4 to 8.6
- fixed `floatx_relative` statement

Version 1.3.0
-------------

- added support for Gappa 1.3.0 (incompatible with prior versions)
- improved support for half-bounded intervals during tree simplification
- proved `neg_fix` and `abs_fix`
- fixed `opp_mibs` statement
- added support for Flocq's `FLX` formats
- improved support for Coq 8.5

Version 1.2.1
-------------

- fixed compilation with Coq 8.5 and/or camlp4

Version 1.2.0
-------------

- moved to Flocq 2.5

Version 1.1.0
-------------

- moved to Flocq 2.4
- added support for Gappa 1.2.0

Version 1.0.0
-------------

- added support for Gappa 1.0.0
- fixed invalid identifiers being sent to Gappa
- fixed broken generalization of terms
- added support for negation, disjunction, and implication
- allowed half-bounded intervals
- proved tree simplification

Version 0.21.1
--------------

- fixed build for the tarball and the tactic

Version 0.21.0
-------------

- added support for Gappa 0.18.0
- added handling of formats to the tactic

Version 0.20.0
--------------

- moved to Coq 8.4

Version 0.19.0
--------------

- switched build system to `remake`
- added support for Gappa 0.17.0
- proved `opp_fibq`, `square`, `bnd_of_bnd_rel`, `bnd_of_rel_bnd`

Version 0.18.0
--------------

- improved error messages for the tactic
- added handling of `bpow` function to the tactic
- added support for Gappa 0.16.0
- proved `eql_of_cst`, `fixed_fix_of_fix`, `float_relative_inv_n?`,
  `float_absolute_inv_n?`, `add_rr`, `sub_rr`, `bnd_div_of_rel_bnd_div`
- removed the file containing proxy theorems

Version 0.17.0
--------------

- moved to Flocq 2.0

Version 0.16.0
--------------

- added support for Gappa 0.15.0
- proved `fix_float_of_fix`, `fixed_error_ne`, `neg_a`
- removed conversion of equality to null enclosure from the tactic

Version 0.15.0
--------------

- moved to Coq 8.3

Version 0.14.1
--------------

- fixed an incompatibility with Flocq 1.2

Version 0.14
------------

- added dependency on the Flocq library
- removed support for the legacy `gappa` tactic

Version 0.13
------------

- added support for `REL` properties as `|r-e| <= b*|e|` in the gappa tactic

Version 0.12
------------

- imported the OCaml code of the `gappa` tactic in the library
  (support requires Coq 8.2, OCaml 3.11, and Gappa 0.12.0)
- fixed incompatibility between the tactic and glob dumping
- improved tactic with respect to redundant or contradictory hypotheses

Version 0.11
------------

- added support for Gappa 0.11.0
- improved build system

Version 0.10
------------

- fixed an incompatibility with Coq 8.2

Version 0.9
-----------

- prevented `gappa_prepare` from computing on non-reducible bounds
- improved `gappa_prepare` to deal with equality goal

Version 0.8
-----------

- added tactic support for calling Gappa from Coq
- proved `*_subset`, `nzr_of_nzr_rel*`, `div_xals`, `div_fi*`, `addf_*`, `add_fi?q`,
  `sub_fi?q`, `rel_of_equal`
- moved `abs_*`, `*_of_singleton_bnd` theorems to `ABS` predicate
- moved `mul_fi?q`, `div_filq` to `REL` predicate

Version 0.7
-----------

- changed coercions to produce user-friendly constants

Version 0.6
-----------

- proved `rewrite_*` for constraints on user rewriting rules
- proved `subset_*` for half-bounded goals
- proved `intersect_rr`, `absurd_intersect_rr`, and `div_rr` for relative errors
- proved `addf_*` rewriting helpers for relative error of addition
- moved `compose` to relative errors
- adapted to Coq 8.1pl1

Version 0.5
-----------

- improved `sqrt`
- proved `rel_of_fix_float_ne`, `nzr_of_abs`, `nzr_of_bnd`, `bnd_of_nzr_rel`,
  `rel_of_nzr_bnd`, `error_of_rel`, `mul_rr`
- adapted to Coq 8.1

Version 0.4
-----------

- fixed `mul_mibs`
- proved `float_absolute_ne`, `float_absolute_ne_wide`, `float_relative_ne`
- adapted to Coq 8.1gamma

Version 0.3
-----------

- proved `flt_of_float`, `float_of_fix_flt`, `float_enforce`, `flt_of_singleton_bnd`,
  `fix_of_flt_bnd`, `flt_of_fix_bnd`

Version 0.2
-----------

- added error propagation through opposite, division, and square root
- added support for Gappa 0.7.1
- added rounding formalism for `fixed` and `float`
- specialized formalism for `fixed<dn>`
- used a precious variable for `COQC`

Version 0.1
-----------

- added support for Gappa 0.7.0
