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
cppcsp_available=true

#Sets "ac_cv_prog_cc_c99" to "no" if C99 is not supported
AC_PROG_CC_C99
if test "x$ac_cv_prog_cc_c99" = "xno"; then
  AC_MSG_WARN([C99 support not found; output from the C backend will not compile on this machine])
  ccsp_kroc_available=false
fi

#AC_NEED_PROG(progname,progvar)
AC_DEFUN([AC_NEED_PROG],
[
  AC_CHECK_PROG($2,$1,[true],[false])
  if test x$$2 = "xfalse"; then
    AC_MSG_ERROR([$1 not found])
  fi
])

#Check that they have alex, GHC, kroc, svn and the CCSP headers:

AC_NEED_PROG(ghc,HAVE_ghc)
AC_NEED_PROG(ghc-pkg,HAVE_ghcpkg)
AC_NEED_PROG(alex,HAVE_alex)

AC_CHECK_PROG([HAVE_KROC],[kroc],[true],[false])
if test "x$HAVE_KROC" = "xfalse"; then
  AC_MSG_WARN([kroc not found; you will not be able to compile output from the C backend on this machine])
  ccsp_kroc_available=false
  kroc_incpath=
else
  kroc_incpath=`kroc --ccincpath`
fi

AC_CHECK_PROG([HAVE_SVN],[svn],[true],[false])
if test "x$HAVE_SVN" = "xfalse"; then
  AC_MSG_WARN([svn (Subversion) not found; you will not be able to fetch the occam cgtests from the public repository])
fi

AC_CHECK_PROG([HAVE_HADDOCK],[haddock],[true],[false])
if test "x$HAVE_HADDOCK" = "xfalse"; then
  AC_MSG_WARN([haddock not found; you will not be able to generate the documentation from the Tock source code])
fi

#Test that they have the right GHC libraries installed (such as hunit, mtl)

AC_DEFUN([AC_NEED_HASKELL_LIB],
[
  AC_MSG_CHECKING([for Haskell library $1])
  $2=`ghc-pkg list $1 | grep $1`
  if test "x$$2" = "x"; then
    AC_MSG_ERROR([Haskell library $1 not found])
  else
    AC_MSG_RESULT([$$2])
  fi
])

AC_NEED_HASKELL_LIB([mtl],LIB_mtl)
AC_NEED_HASKELL_LIB([HUnit],LIB_hunit)
AC_NEED_HASKELL_LIB([parsec],LIB_parsec)
AC_NEED_HASKELL_LIB([fgl],LIB_fgl)
AC_NEED_HASKELL_LIB([QuickCheck],LIB_quickcheck)
AC_NEED_HASKELL_LIB([regex-base],LIB_regexbase)
AC_NEED_HASKELL_LIB([regex-compat],LIB_regexcompat)
AC_NEED_HASKELL_LIB([regex-posix],LIB_regexposix)

AC_LANG(C)
old_CFLAGS="$CFLAGS"
old_CPPFLAGS="$CPPFLAGS"
CFLAGS="$kroc_incpath"
CPPFLAGS="$kroc_incpath"
AC_CHECK_HEADER([cifccsp.h],[HAVE_CIFCCSP=true],[HAVE_CIFCCSP=false])

if test "x$HAVE_CIFCCSP" = "xfalse"; then
  AC_MSG_WARN([cifccsp.h not found; you will not be able to compile output from the C backend on this machine])
  ccsp_kroc_available=false
fi
CFLAGS="$old_CFLAGS"
CPPFLAGS="$old_CPPFLAGS"

#Must remember to switch the language to C++ before checking the C++ headers:
AC_LANG(C++)
AC_CHECK_HEADERS([cppcsp/cppcsp.h],[HAVE_CPPCSP=true],[HAVE_CPPCSP=false])
if test "x$HAVE_CPPCSP" = "xfalse"; then
  AC_MSG_WARN([cppcsp/cppcsp.h not found; you will not be able to compile output from the C++ backend on this machine])
  cppcsp_available=false
fi

#Warn them if neither backend is available:
if test "x$cppcsp_available$ccsp_kroc_available" = "xfalsefalse"; then
  AC_MSG_WARN([No working backends: Code from neither the C nor C++ backend will compile on your machine])
fi


#Check whether their compiler supports the -fgnu89-inline flag:
#Must use the C language for this:
AC_LANG(C)
AC_MSG_CHECKING([whether -fgnu89-inline flag is accepted])
old_CFLAGS="$CFLAGS"
CFLAGS="-fgnu89-inline"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  gnu89_inline=-fgnu89-inline
  ,
  AC_MSG_RESULT([no])
  gnu89_inline=
)
CFLAGS="$old_CFLAGS"

AC_MSG_CHECKING([Checking GHC version])

ghc_version=`ghc --numeric-version`
ghc_version_major=`echo $ghc_version |  awk -F . '{print $1}'`
ghc_version_mid=`echo $ghc_version |  awk -F . '{print $2}'`
ghc_version_minor=`echo $ghc_version |  awk -F . '{print $3}'`

AC_MSG_RESULT($ghc_version_major.$ghc_version_mid.$ghc_version_minor)

AC_MSG_CHECKING([Checking that GHC version is at least 6.6.x])

if test $ghc_version_major -lt 6 -o $ghc_version_mid -lt 6; then
	AC_MSG_ERROR([GHC of at least version 6.6.x is required])
else
	AC_MSG_RESULT([ok])
fi

AM_CONDITIONAL([GHC68],[test $ghc_version_major -ge 6 -a $ghc_version_mid -ge 8])

AC_SUBST(gnu89_inline)
AC_SUBST(ccsp_kroc_available)
AC_SUBST(cppcsp_available)
AC_SUBST(MKDIR_P)

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
