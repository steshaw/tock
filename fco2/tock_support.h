// C99 support definitions for Tock.
// vim:set foldmethod=marker:

#ifndef TOCK_SUPPORT_H
#define TOCK_SUPPORT_H

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <limits.h>
#include <float.h>
#include <stdio.h>
#include <math.h>

#include <cifccsp.h>

//{{{ mostneg/mostpos
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
//}}}

//{{{ compiler-specific attributes
#ifdef __GNUC__
#define occam_struct_packed __attribute__ ((packed))
#define occam_unused __attribute__ ((unused))
#else
#warning No PACKED (or other compiler specials) implementation for this compiler
#define occam_struct_packed
#define occam_unused
#endif
//}}}

//{{{ runtime check functions
#define occam_stop(pos, format, args...) \
	do { \
		EXTERNAL_CALLN (fprintf, stderr, "Program stopped at %s: " format "\n", pos, ##args); \
		SetErr (); \
	} while (0)

static int occam_check_slice (int, int, int, const char *) occam_unused;
static int occam_check_slice (int start, int count, int limit, const char *pos) {
	int end = start + count;
	if (count != 0 && (start < 0 || start >= limit
	                   || end < 0 || end > limit
	                   || count < 0)) {
		occam_stop (pos, "invalid array slice from %d to %d (should be 0 <= i <= %d)", start, end, limit);
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
//}}}

//{{{ type-specific runtime checks
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
//}}}

//{{{ conversions to and from reals
// FIXME: Again, all these should check.

//{{{ float
float occam_convert_int64_t_float_round (int64_t, const char *) occam_unused;
float occam_convert_int64_t_float_round (int64_t v, const char *pos) {
	return (float) v;
}

float occam_convert_int64_t_float_trunc (int64_t, const char *) occam_unused;
float occam_convert_int64_t_float_trunc (int64_t v, const char *pos) {
	return (float) v;
}

int64_t occam_convert_float_int64_t_round (float, const char *) occam_unused;
int64_t occam_convert_float_int64_t_round (float v, const char *pos) {
	return (int64_t) v;
}

int64_t occam_convert_float_int64_t_trunc (float, const char *) occam_unused;
int64_t occam_convert_float_int64_t_trunc (float v, const char *pos) {
	return (int64_t) v;
}

float occam_convert_double_float_round (double, const char *) occam_unused;
float occam_convert_double_float_round (double v, const char *pos) {
	return (float) v;
}

float occam_convert_double_float_trunc (double, const char *) occam_unused;
float occam_convert_double_float_trunc (double v, const char *pos) {
	return (float) v;
}
//}}}
//{{{ double
double occam_convert_int64_t_double_round (int64_t, const char *) occam_unused;
double occam_convert_int64_t_double_round (int64_t v, const char *pos) {
	return (double) v;
}

double occam_convert_int64_t_double_trunc (int64_t, const char *) occam_unused;
double occam_convert_int64_t_double_trunc (int64_t v, const char *pos) {
	return (double) v;
}

int64_t occam_convert_double_int64_t_round (double, const char *) occam_unused;
int64_t occam_convert_double_int64_t_round (double v, const char *pos) {
	return (int64_t) v;
}

int64_t occam_convert_double_int64_t_trunc (double, const char *) occam_unused;
int64_t occam_convert_double_int64_t_trunc (double v, const char *pos) {
	return (int64_t) v;
}
//}}}
//}}}

//{{{ intrinsics
// FIXME These should do range checks.

static float occam_SQRT (float, const char *) occam_unused;
static float occam_SQRT (float v, const char *pos) {
	return sqrtf (v);
}

static double occam_DSQRT (double, const char *) occam_unused;
static double occam_DSQRT (double v, const char *pos) {
	return sqrt (v);
}
//}}}

#endif
