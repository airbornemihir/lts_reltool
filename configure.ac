AC_INIT(relts,1.0)
AC_CONFIG_MACRO_DIR([m4])
AM_INIT_AUTOMAKE([foreign])

AC_PROG_CXX
AX_CXX_COMPILE_STDCXX_11

AC_PROG_OCAML
if test "$OCAMLC" = "no"; then
  AC_MSG_ERROR([You must install the OCaml compiler])
fi

AC_PROG_FINDLIB
if test "$OCAMLFIND" = "no"; then
  AC_MSG_ERROR([You must install OCaml findlib (the ocamlfind
  command)])
fi

AC_CHECK_OCAML_PKG([ocamlgraph])
if test "$OCAML_PKG_ocamlgraph" = "no"; then
  AC_MSG_ERROR([Please install OCaml findlib module 'ocamlgraph'.])
fi

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
