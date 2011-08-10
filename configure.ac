AC_INIT([Tock],[0.0.1],[tock-discuss@kent.ac.uk],[tock])
AC_PREREQ([2.60])
AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE

#Store the mkdir -p command:
AC_PROG_MKDIR_P

#Check the user has specified a valid srcdir
AC_CONFIG_SRCDIR(Main.hs)

#Find the C and C++ compilers
AC_PROG_CC
AC_PROG_CXX
AM_PROG_CC_C_O

ccsp_available=true
cppcsp_available=true

#Sets "ac_cv_prog_cc_c99" to "no" if C99 is not supported
AC_PROG_CC_C99
if test "x$ac_cv_prog_cc_c99" = "xno"; then
  AC_MSG_WARN([C99 support not found; output from the C backend will not compile on this machine])
  ccsp_available=false
fi

#TOCK_NEED_PROG(progname,progvar)
AC_DEFUN([TOCK_NEED_PROG],
[
  AC_CHECK_PROG($2,$1,[true],[false])
  if test x$$2 = "xfalse"; then
    AC_MSG_ERROR([$1 not found])
  fi
])

#Check that they have alex, GHC, svn and the CCSP headers:

TOCK_NEED_PROG(ghc,HAVE_ghc)
AC_PATH_PROG(GHC,ghc)
TOCK_NEED_PROG(ghc-pkg,HAVE_ghcpkg)
TOCK_NEED_PROG(alex,HAVE_alex)

AC_CHECK_PROG([HAVE_SVN],[svn],[true],[false])
if test "x$HAVE_SVN" = "xfalse"; then
  AC_MSG_WARN([svn (Subversion) not found; you will not be able to fetch the occam cgtests from the public repository])
fi

AC_CHECK_PROG([HAVE_HADDOCK],[haddock],[true],[false])
if test "x$HAVE_HADDOCK" = "xfalse"; then
  AC_MSG_WARN([haddock not found; you will not be able to generate the documentation from the Tock source code])
fi

#Test that they have the right GHC libraries installed (such as hunit, mtl)

AC_DEFUN([TOCK_NEED_HASKELL_LIB],
[
  AC_MSG_CHECKING([for Haskell library $1])
  $2=`ghc-pkg list $1 | grep $1`
  if test "x$$2" = "x"; then
    AC_MSG_ERROR([Haskell library $1 not found])
  else
    AC_MSG_RESULT([$$2])
  fi
])

TOCK_NEED_HASKELL_LIB([array],LIB_array)
TOCK_NEED_HASKELL_LIB([base],LIB_base)
TOCK_NEED_HASKELL_LIB([containers],LIB_containers)
TOCK_NEED_HASKELL_LIB([directory],LIB_directory)
TOCK_NEED_HASKELL_LIB([mtl],LIB_mtl)
TOCK_NEED_HASKELL_LIB([HUnit],LIB_hunit)
TOCK_NEED_HASKELL_LIB([parsec],LIB_parsec)
TOCK_NEED_HASKELL_LIB([pretty],LIB_pretty)
TOCK_NEED_HASKELL_LIB([fgl],LIB_fgl)
TOCK_NEED_HASKELL_LIB([process],LIB_process)
TOCK_NEED_HASKELL_LIB([QuickCheck],LIB_quickcheck)
TOCK_NEED_HASKELL_LIB([random],LIB_random)
TOCK_NEED_HASKELL_LIB([regex-base],LIB_regexbase)
TOCK_NEED_HASKELL_LIB([regex-compat],LIB_regexcompat)
TOCK_NEED_HASKELL_LIB([regex-posix],LIB_regexposix)

ghc_version=`ghc --numeric-version | awk -F . '{printf "%d%03d%03d\n", $1, $2, $3}'`

AC_MSG_CHECKING([whether GHC version is reasonable])
if test $ghc_version -lt 6012000; then
	AC_MSG_ERROR([GHC 6.12 or later is required])
fi
AC_MSG_RESULT([OK])

AC_DEFUN([TOCK_PICK_HASKELL_LIB_VER],
[
  AC_MSG_CHECKING([for $1 library, major version $2])
  $3=`ghc-pkg list $1 | grep $1 | grep -oE "$1-$2[[.0-9]]+" | tail -n 1`
  if test "x$$3" = "x"; then
    AC_MSG_ERROR([$1-$2* not found])
  else
    AC_MSG_RESULT([$$3])
  fi
])

TOCK_PICK_HASKELL_LIB_VER([base],[4],[LIB_VER_base])
TOCK_PICK_HASKELL_LIB_VER([syb],[0],LIB_VER_syb)

PKG_CHECK_MODULES(CCSP, ccsp-1.6 >= 1.6.3,,
	AC_MSG_WARN([CCSP not located using pkg-config; you will not be able to compile output from the C backend on this machine: ] $CCSP_PKG_ERRORS)
	ccsp_available=false
)

PKG_CHECK_MODULES(CPPCSP2,cppcsp2-2.0 >= 2.0.4,,
	AC_MSG_WARN([C++CSP2 backend not located using pkg-config; you will not be able to compile output from the C++ backend on this machine: ] $CPPCSP2_PKG_ERRORS)
	cppcsp_available=false
)

PKG_CHECK_MODULES(GLIB,glib-2.0 >= 2.4.0,,
	AC_MSG_WARN([Glib not available; you will not be able to compile output from the C backend on this machine: ] $GLIB_PKG_ERRORS)
	ccsp_kroc_available=false
)

#Must remember to switch the language to C++ before checking the C++ headers:
AC_LANG(C++)
CPPFLAGS="$CPPCSP2_CFLAGS"
AC_CHECK_HEADERS([cppcsp/cppcsp.h],[HAVE_CPPCSP=true],[HAVE_CPPCSP=false])
if test "x$HAVE_CPPCSP" = "xfalse"; then
  AC_MSG_WARN([cppcsp/cppcsp.h not found; you will not be able to compile output from the C++ backend on this machine])
  cppcsp_available=false
fi

#Warn them if neither backend is available:
if test "x$cppcsp_available$ccsp_available" = "xfalsefalse"; then
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

#Check whether GCC accepts the -fno-strict-overflow setting:
AC_MSG_CHECKING([whether -fno-strict-overflow flag is accepted])
CFLAGS="-fno-strict-overflow"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  no_strict_overflow=-fno-strict-overflow
  ,
  AC_MSG_RESULT([no])
  no_strict_overflow=
)

#Check whether GCC accepts the -fno-strict-aliasing setting:
AC_MSG_CHECKING([whether -fno-strict-aliasing flag is accepted])
CFLAGS="-fno-strict-aliasing"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  no_strict_aliasing=-fno-strict-aliasing
  ,
  AC_MSG_RESULT([no])
  no_strict_aliasing=
)

#Check whether GCC accepts the -fno-tree-vrp setting:
AC_MSG_CHECKING([whether -fno-tree-vrp flag is accepted])
CFLAGS="-fno-tree-vrp"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  no_tree_vrp=-fno-tree-vrp
  ,
  AC_MSG_RESULT([no])
  no_tree_vrp=
)

#Check whether GCC accepts the -Wno-unused-parameter -Wno-unused-variable flags:
AC_MSG_CHECKING([whether -Wno-unused-parameter and -Wno-unused-variable flags are accepted])
CFLAGS="-Wno-unused-parameter -Wno-unused-variable"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  no_unused="-Wno-unused-parameter -Wno-unused-variable"
  ,
  AC_MSG_RESULT([no])
  no_unused=
)

#Check whether GCC accepts the -Werror=cast-qual option
AC_MSG_CHECKING([whether -Werror=cast-qual flag is accepted])
CFLAGS="-Werror=cast-qual"
AC_COMPILE_IFELSE(AC_LANG_PROGRAM([[ ]]),
  AC_MSG_RESULT([yes])
  warn_error="-Werror=cast-qual"
  ,
  AC_MSG_RESULT([no])
  warn_error=
)


CFLAGS="$old_CFLAGS"


# Check the sizes of certain constructs.  We'll need to be cleverer if in future
# we want to allow cross-compilation.

AC_LANG(C++)
AC_CHECK_SIZEOF(bool)
AC_COMPUTE_INT(CXX_BOOL_SIZE,SIZEOF_BOOL)
AC_SUBST(CXX_BOOL_SIZE)
AC_LANG(C)
AC_CHECK_SIZEOF(_Bool)
AC_COMPUTE_INT(C_BOOL_SIZE,SIZEOF__BOOL)
AC_SUBST(C_BOOL_SIZE)

#We use sizeof(void*) to work out the size for INT,
#because the C int type is 32-bit on both 32-bit and 64-bit platforms (with GCC, x86/x86-64).
AC_CHECK_SIZEOF(void*)
AC_COMPUTE_INT(C_INT_SIZE,SIZEOF_VOIDP)
AC_SUBST(C_INT_SIZE)

if test "x$C_INT_SIZE" = "x2"; then
C_INT_EQUIV=Int16
fi
if test "x$C_INT_SIZE" = "x4"; then
C_INT_EQUIV=Int32
fi
if test "x$C_INT_SIZE" = "x8"; then
C_INT_EQUIV=Int64
fi
AC_SUBST(C_INT_EQUIV)

CFLAGS="$CFLAGS $no_strict_overflow $no_tree_vrp"
# The reason for -fno-strict-overflow and -fno-tree-vrp above is that with the way I have implemented
# range checking, on GCC 4.3.2 (and probably other versions), GCC has
# a bug triggered that causes invalid behaviour (spurious overflows can happen)
# when compiled with -O2.  One mitigation I have found is to turn off these
# particular optimisations.  Since GCC 4.3.2 will be around for a long time,
# we have to leave in -fno-tree-vrp and -fno-strict-overflow for a long time too.
#
# ... and the bug is still present as of GCC 4.6:
#   http://gcc.gnu.org/bugzilla/show_bug.cgi?id=35634
#
# UPDATE: According to my GCC bug, http://gcc.gnu.org/bugzilla/show_bug.cgi?id=38929
# this problem can be fixed instead by changing my x++ into x+=1 in my code.  I've done
# that, but I'm also leaving these flags in so that any other code (for example,
# that Tock might spit out) that uses increments doesn't have the same issue.

# We don't use $warn_error because it stops us passing const pointers
# (for example, from pulling things up) being released when they are
# mobiles.  Perhaps in future we should drop const modifiers on mobile stuff.

common_cflags="-Wall $no_unused -ggdb3 -Isupport $no_strict_aliasing"

TOCK_CFLAGS="$gnu89_inline $CPPFLAGS $CFLAGS $common_cflags $CCSP_CFLAGS $GLIB_CFLAGS"
TOCK_CLDFLAGS="$LDFLAGS $CCSP_LIBS $GLIB_LIBS -lm"

TOCK_CXXFLAGS="$CPPFLAGS $CXXFLAGS $common_cflags $CPPCSP2_CFLAGS"
TOCK_CXXLDFLAGS="$LDFLAGS $CPPCSP2_LIBS -lm"

DATADIR=$datadir
AC_SUBST(DATADIR)

AC_SUBST(TOCK_CFLAGS)
AC_SUBST(TOCK_CLDFLAGS)
AC_SUBST(TOCK_CXXFLAGS)
AC_SUBST(TOCK_CXXLDFLAGS)

AC_SUBST(ccsp_available)
AC_SUBST(cppcsp_available)
AC_SUBST(MKDIR_P)
AC_SUBST(LIB_VER_base)
AC_SUBST(LIB_VER_quickcheck)
AC_SUBST(LIB_VER_syb)

AC_CONFIG_FILES([Makefile config/TypeSizes.hs config/CompilerCommands.hs])
AC_OUTPUT
