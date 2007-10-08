AC_INIT([Tock],[0.0.1],[tock-discuss@kent.ac.uk],[tock])
AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE

#Store the mkdir -p command:
AC_PROG_MKDIR_P

#Check the user has specified a valid srcdir
AC_CONFIG_SRCDIR(Main.hs)

#Find the C and C++ compilers
AC_PROG_CC
AC_PROG_CXX

ccsp_kroc_available=true

#Sets "ac_cv_prog_cc_c99" to "no" if C99 is not supported
AC_PROG_CC_C99
if test "x$ac_cv_prog_cc_c99" = "xno"; then
  AC_MSG_WARN([C99 support not found; output from the C backend will not compile on this machine])
  ccsp_kroc_available=false
fi

#Check that they have alex, GHC, kroc, and the CCSP headers:
AC_CHECK_PROG([HAVE_GHC],[ghc],[true],[false])
if test "x$HAVE_GHC" = "xfalse"; then
  AC_MSG_ERROR([ghc not found])
fi

AC_CHECK_PROG([HAVE_ALEX],[alex],[true],[false])
if test "x$HAVE_ALEX" = "xfalse"; then
  AC_MSG_ERROR([alex not found])
fi

AC_CHECK_PROG([HAVE_KROC],[kroc],[true],[false])
if test "x$HAVE_KROC" = "xfalse"; then
  AC_MSG_WARN([kroc not found; you will not be able to compile output from the C backend on this machine])
  ccsp_kroc_available=false
fi

AC_LANG(C)
AC_CHECK_HEADER([cifccsp.h],[HAVE_CIFCCSP=true],[HAVE_CIFCCSP=false])

if test "x$HAVE_CIFCCSP_H" = "xfalse"; then
  AC_MSG_WARN([cifccsp.h not found; you will not be able to compile output from the C backend on this machine])
  ccsp_kroc_available=false
fi

#Using AC_CHECK_HEADER for the C++CSP file dies because autoconf attempts to compile it in a C program, which doesn't like the C++.
#Therefore I just test it using the preprocessor:

AC_LANG(C++)
AC_CHECK_HEADERS([cppcsp/cppcsp.h],[HAVE_CPPCSP=true],[HAVE_CPPCSP=false])
if test "x$HAVE_CPPCSP_H" = "xfalse"; then
  AC_MSG_WARN([cppcsp/cppcsp.h not found; you will not be able to compile output from the C++ backend on this machine])
  cppcsp_available=false
fi

#Warn them if neither backend is available:
if test "x$cppcsp_available$ccsp_kroc_available" = "xfalsefalse"; then
  AC_MSG_WARN([No working backends: Code from neither the C nor C++ backend will compile on your machine])
fi


#Check whether their compiler supports the -fgnu89-inline flag:
AC_LANG(C)
AC_MSG_CHECKING([whether -fgnu89-inline flag is accepted])
CFLAGS="-fgnu89-inline"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  gnu89_inline=-fgnu89-inline
  ,
  AC_MSG_RESULT([no])
  gnu89_inline=
)

AC_SUBST(gnu89_inline)
AC_SUBST(ccsp_kroc_available)
AC_SUBST(cppcsp_available)
AC_SUBST(MKDIR_P)

AC_OUTPUT(Makefile)
