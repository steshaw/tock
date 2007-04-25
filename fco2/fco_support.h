// C99 support definitions for FCO.

#ifndef FCO_SUPPORT_H
#define FCO_SUPPORT_H

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <limits.h>
#include <float.h>
#include <stdio.h>

#include <cifccsp.h>

#define occam_mostneg_bool false
#define occam_mostpos_bool true
#define occam_mostneg_char CHAR_MIN
#define occam_mostpos_char CHAR_MAX
#define occam_mostneg_int INT_MIN
#define occam_mostpos_int INT_MAX
#define occam_mostneg_int16_t INT16_MIN
#define occam_mostpos_int16_t INT16_MAX
#define occam_mostneg_int32_t INT32_MIN
#define occam_mostpos_int32_t INT32_MAX
#define occam_mostneg_int64_t INT64_MIN
#define occam_mostpos_int64_t INT64_MAX
#define occam_mostneg_float -FLT_MAX
#define occam_mostpos_float FLT_MAX
#define occam_mostneg_double -DBL_MAX
#define occam_mostpos_double DBL_MAX

#ifdef __GNUC__
#define occam_struct_packed __attribute__ ((packed))
#define occam_unused __attribute__ ((unused))
#else
#warning No PACKED (or other compiler specials) implementation for this compiler
#define occam_struct_packed
#define occam_unused
#endif

#define occam_stop(pos, format, args...) \
	do { \
		EXTERNAL_CALLN (fprintf, stderr, "Program stopped at %s: " format "\n", pos, ##args); \
		SetErr (); \
	} while (0)

static int occam_check_slice (int, int, int, const char *) occam_unused;
static int occam_check_slice (int start, int count, int limit, const char *pos) {
	int end = start + count;
	if (end < 0 || end > limit) {
		occam_stop (pos, "invalid array slice from %d to %d (end should be 0 <= i <= %d)", start, end, limit);
	}
	return count;
}
static int occam_check_index (int, int, const char *) occam_unused;
static int occam_check_index (int i, int limit, const char *pos) {
	if (i < 0 || i >= limit) {
		occam_stop (pos, "invalid array index %d (should be 0 <= i < %d)", i, limit);
	}
	return i;
}

#define MAKE_RANGE_CHECK(type, format) \
	static type occam_range_check_##type (type, type, type, const char *) occam_unused; \
	static type occam_range_check_##type (type lower, type upper, type n, const char *pos) { \
		if (n < lower || n > upper) { \
			occam_stop (pos, "invalid value in conversion " format " (should be " format " <= i <= " format ")", n, lower, upper); \
		} \
		return n; \
	}
// FIXME All of these need to check for overflow and report errors appropriately.
#define MAKE_ADD(type) \
	static type occam_add_##type (type, type, const char *) occam_unused; \
	static type occam_add_##type (type a, type b, const char *pos) { \
		return a + b; \
	}
#define MAKE_SUBTR(type) \
	static type occam_subtr_##type (type, type, const char *) occam_unused; \
	static type occam_subtr_##type (type a, type b, const char *pos) { \
		return a - b; \
	}
#define MAKE_MUL(type) \
	static type occam_mul_##type (type, type, const char *) occam_unused; \
	static type occam_mul_##type (type a, type b, const char *pos) { \
		return a * b; \
	}
#define MAKE_DIV(type) \
	static type occam_div_##type (type, type, const char *) occam_unused; \
	static type occam_div_##type (type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, "divide by zero"); \
		} \
		return a / b; \
	}
#define MAKE_REM(type) \
	static type occam_rem_##type (type, type, const char *) occam_unused; \
	static type occam_rem_##type (type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, "modulo by zero"); \
		} \
		return a % b; \
	}

//{{{ char
MAKE_RANGE_CHECK(char, "%d")
MAKE_ADD(char)
MAKE_SUBTR(char)
MAKE_MUL(char)
MAKE_DIV(char)
MAKE_REM(char)
//}}}
//{{{ int16_t
MAKE_RANGE_CHECK(int16_t, "%d")
MAKE_ADD(int16_t)
MAKE_SUBTR(int16_t)
MAKE_MUL(int16_t)
MAKE_DIV(int16_t)
MAKE_REM(int16_t)
//}}}
//{{{ int
MAKE_RANGE_CHECK(int, "%d")
MAKE_ADD(int)
MAKE_SUBTR(int)
MAKE_MUL(int)
MAKE_DIV(int)
MAKE_REM(int)
//}}}
//{{{ int32_t
MAKE_RANGE_CHECK(int32_t, "%d")
MAKE_ADD(int32_t)
MAKE_SUBTR(int32_t)
MAKE_MUL(int32_t)
MAKE_DIV(int32_t)
MAKE_REM(int32_t)
//}}}
//{{{ int64_t
MAKE_RANGE_CHECK(int64_t, "%lld")
MAKE_ADD(int64_t)
MAKE_SUBTR(int64_t)
MAKE_MUL(int64_t)
MAKE_DIV(int64_t)
MAKE_REM(int64_t)
//}}}
// FIXME range checks for float and double shouldn't work this way
//{{{ float
MAKE_RANGE_CHECK(float, "%d")
MAKE_ADD(float)
MAKE_SUBTR(float)
MAKE_MUL(float)
MAKE_DIV(float)
//}}}
//{{{ double
MAKE_RANGE_CHECK(double, "%d")
MAKE_ADD(double)
MAKE_SUBTR(double)
MAKE_MUL(double)
MAKE_DIV(double)
//}}}

#undef MAKE_RANGE_CHECK
#undef MAKE_ADD
#undef MAKE_SUBTR
#undef MAKE_MUL
#undef MAKE_DIV
#undef MAKE_REM

#endif
