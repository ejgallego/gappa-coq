AC_INIT([Coq support library for Gappa], [0.15.0],
        [Guillaume Melquiond <guillaume.melquiond@inria.fr>],
        [gappalib-coq])
AM_INIT_AUTOMAKE

m4_divert_push(99)
if test "$ac_init_help" = "long"; then
  ac_init_help=short
fi
m4_divert_pop(99)

m4_divert_push([HELP_ENABLE])
Fine tuning of the installation directory:
AS_HELP_STRING([--libdir=DIR], [library @<:@DIR=`$COQC -where`/user-contrib/Gappa@:>@])
m4_divert_pop([HELP_ENABLE])

AC_DEFUN([AX_VERSION_GE], [
  cmp_ver_sed=['s/\([0-9]\+\)/%\1%/g;s/%\([0-9]\)%/%00\1%/g;s/%\([0-9][0-9]\)%/%0\1%/g;s/[^0-9]//g']
  cmp_ver_1=`echo "$1" | sed -e "$cmp_ver_sed"`
  cmp_ver_2=`echo "$2" | sed -e "$cmp_ver_sed"`
  cmp_ver_3="$cmp_ver_1`echo $cmp_ver_2 | sed -e 's/./0/g'`"
  cmp_ver_4="$cmp_ver_2`echo $cmp_ver_1 | sed -e 's/./0/g'`"
  if test "0$cmp_ver_3" -ge "0$cmp_ver_4" ; then
    m4_ifvaln([$3],[$3],[:])dnl
    m4_ifvaln([$4],[else $4])dnl
  fi
])

native_tactic=yes
byte_tactic=yes

AC_ARG_VAR(COQC, [Coq compiler command [coqc]])
AC_MSG_CHECKING([for coqc >= 8.3])
if test ! "$COQC"; then COQC=`which coqc`; fi
coqc_version=[`"$COQC" -v | sed -n -e 's/^.*version \([0-9.]\+\).*$/\1/p'`]
AX_VERSION_GE([$coqc_version], [8.3],
  [ AC_MSG_RESULT([$COQC]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find Coq (http://coq.inria.fr/)]) ])

AC_ARG_VAR(COQDEP, [Coq dependency analyzer command [coqdep]])
AC_PATH_TOOL(COQDEP, coqdep)

AC_ARG_VAR(OCAMLC, [OCaml compiler command [ocamlc]])
AC_PATH_TOOL(OCAMLC, ocamlc)

AC_ARG_VAR(CAMLP4, [OCaml preprocessor [camlp5]])
AC_PATH_TOOL(CAMLP4, camlp5)

AC_ARG_VAR(OCAMLOPT, [OCaml compiler command [ocamlopt]])
AC_CACHE_CHECK([for ocamlopt >= 3.11], [gappa_cv_ocamlopt], [
  if test "$OCAMLOPT"; then
    gappa_cv_ocamlopt="$OCAMLOPT"
  else
    ocamlopt_path=`which ocamlopt`
    if test -n "$ocamlopt_path"; then
      ocamlopt_version=`"$ocamlopt_path" -version`
      AX_VERSION_GE([$ocamlopt_version], [3.11], [gappa_cv_ocamlopt="$ocamlopt_path"])
    fi
  fi ])
OCAMLOPT="$gappa_cv_ocamlopt"

if test -z "$OCAMLOPT"; then native_tactic=no; fi

AC_MSG_CHECKING([for Flocq])
AS_IF(
  [ echo "Require Fcore Fcalc_digits." > conftest.v
    "$COQC" conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find the Flocq library (http://flocq.gforge.inria.fr/)])])
rm -f conftest.v conftest.vo conftest.err

AC_SUBST(COQLIBS)
COQLIBS=`$COQC -where`

if test "$libdir" = '${exec_prefix}/lib'; then
  libdir="$COQLIBS/user-contrib/Gappa"
fi

AC_SUBST(COQRFLAG, ['-R . Gappa'])
AC_ARG_ENABLE([prefix], AS_HELP_STRING([--disable-prefix], [do not compile files into a Gappa module]),
  [if test "$enable_prefix" = "no"; then COQRFLAG= ; fi], [])

AC_ARG_ENABLE([tactic],
  AS_HELP_STRING([--disable-tactic], [do not compile a "gappa" tactic]),
  [if test "$enable_tactic" = "no"; then native_tactic=no ; byte_tactic=no ; fi], [])

AC_ARG_ENABLE([native-tactic],
  AS_HELP_STRING([--disable-native-tactic], [do not compile a native "gappa" tactic]),
  [if test "$enable_native_tactic" = "no"; then native_tactic=no ; fi], [])

AC_ARG_ENABLE([byte-tactic],
  AS_HELP_STRING([--disable-byte-tactic], [do not compile a bytecode "gappa" tactic]),
  [if test "$enable_byte_tactic" = "no"; then byte_tactic=no ; fi], [])

if test "x$COQRFLAGS" = x; then module_name=Gappa; else module_name=none; fi

AC_SUBST(TACTIC_TARGETS)
AC_SUBST(TACTIC_PARAM)

tactic_mode=""
if test "$native_tactic" = yes; then
  tactic_mode="$tactic_mode native"
  TACTIC_TARGETS="$TACTIC_TARGETS gappatac.cmxs"
  if test "$byte_tactic" = no; then
    TACTIC_PARAM="-opt"
  fi
fi
if test "$byte_tactic" = yes; then
  tactic_mode="$tactic_mode bytecode"
  TACTIC_TARGETS="$TACTIC_TARGETS gappatac.cmo"
  if test "$native_tactic" = no; then
    TACTIC_PARAM="-byte"
  fi
fi

if test -z "$tactic_mode"; then tactic_mode=" none"; fi

echo
echo "=== Summary ==="
echo "Installation directory   $libdir"
echo "Module name              $module_name"
echo "Gappa tactic            $tactic_mode"
echo

AC_CONFIG_FILES([Makefile src/Makefile testsuite/Makefile])
AC_OUTPUT
