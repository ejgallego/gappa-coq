AC_INIT([Coq support library for Gappa], [0.1],
        [Guillaume Melquiond <guillaume.melquiond@ens-lyon.fr>],
        [gappalib-coq])
AM_INIT_AUTOMAKE

COQC=coqc
AC_ARG_WITH([coqc], AS_HELP_STRING([--with-coqc=PATH], [location of the coqc binary]),
	[COQC="$withval"])
AC_SUBST([COQC])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
