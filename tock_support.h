/*
 * C99 support code for Tock programs
 * Copyright (C) 2007  University of Kent
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
 * General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef TOCK_SUPPORT_H
#define TOCK_SUPPORT_H

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <limits.h>
#include <float.h>
#include <stdio.h>
#include <math.h>

//For C++CSP:
#ifndef NO_CIFCCSP
#include <cifccsp.h>
#else
#define EXTERNAL_CALLN(F,I,args...)     (F)((I),##args)
#define EXTERNAL_CALL(F)                (F)()
#define SetErr()                        
#define Channel int
#endif

//{{{ mostneg/mostpos
#define occam_mostneg_bool false
#define occam_mostpos_bool true
#define occam_mostneg_uint8_t 0
#define occam_mostpos_uint8_t UINT8_MAX
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

//{{{ helper functions to simplify the code generation
static inline void tock_init_chan_array(Channel*, Channel**, int) occam_unused;
static inline void tock_init_chan_array(Channel* pointTo, Channel** pointFrom, int count) {
	for (int i = 0; i < count; i++) {
		pointFrom[i] = &(pointTo[i]);
	}	
}

//}}}

//{{{ runtime check functions

//C++CSP may have defined this function already:
#ifndef occam_stop
#define occam_stop(pos, format, args...) \
	do { \
		EXTERNAL_CALLN (fprintf, stderr, "Program stopped at %s: " format "\n", pos, ##args); \
		SetErr (); \
	} while (0)
#endif //occam_stop

static inline int occam_check_slice (int, int, int, const char *) occam_unused;
static inline int occam_check_slice (int start, int count, int limit, const char *pos) {
	int end = start + count;
	if (count != 0 && (start < 0 || start >= limit
	                   || end < 0 || end > limit
	                   || count < 0)) {
		occam_stop (pos, "invalid array slice from %d to %d (should be 0 <= i <= %d)", start, end, limit);
	}
	return count;
}
static inline int occam_check_index (int, int, const char *) occam_unused;
static inline int occam_check_index (int i, int limit, const char *pos) {
	if (i < 0 || i >= limit) {
		occam_stop (pos, "invalid array index %d (should be 0 <= i < %d)", i, limit);
	}
	return i;
}
static inline int occam_check_retype (int, int, const char *) occam_unused;
static inline int occam_check_retype (int src, int dest, const char *pos) {
	if (src % dest != 0) {
		occam_stop (pos, "invalid size for RETYPES/RESHAPES (%d does not divide into %d)", dest, src);
	}
	return src / dest;
}
//}}}

//{{{ type-specific arithmetic ops and runtime checks
#define MAKE_RANGE_CHECK(type, format) \
	static inline type occam_range_check_##type (type, type, type, const char *) occam_unused; \
	static inline type occam_range_check_##type (type lower, type upper, type n, const char *pos) { \
		if (n < lower || n > upper) { \
			occam_stop (pos, "invalid value in conversion " format " (should be " format " <= i <= " format ")", n, lower, upper); \
		} \
		return n; \
	}
// FIXME All of these need to check for overflow and report errors appropriately.
#define MAKE_ADD(type) \
	static inline type occam_add_##type (type, type, const char *) occam_unused; \
	static inline type occam_add_##type (type a, type b, const char *pos) { \
		return a + b; \
	}
#define MAKE_SUBTR(type) \
	static inline type occam_subtr_##type (type, type, const char *) occam_unused; \
	static inline type occam_subtr_##type (type a, type b, const char *pos) { \
		return a - b; \
	}
#define MAKE_MUL(type) \
	static inline type occam_mul_##type (type, type, const char *) occam_unused; \
	static inline type occam_mul_##type (type a, type b, const char *pos) { \
		return a * b; \
	}
#define MAKE_DIV(type) \
	static inline type occam_div_##type (type, type, const char *) occam_unused; \
	static inline type occam_div_##type (type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, "divide by zero"); \
		} \
		return a / b; \
	}
#define MAKE_NEGATE(type) \
	static inline type occam_negate_##type (type, const char *) occam_unused; \
	static inline type occam_negate_##type (type a, const char *pos) { \
		return - a; \
	}
// occam's \ doesn't behave like C's %; it handles negative arguments.
// (Effectively it ignores signs coming in, and the output sign is the sign of
// the first argument.)
#define MAKE_REM(type) \
	static inline type occam_rem_##type (type, type, const char *) occam_unused; \
	static inline type occam_rem_##type (type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, "modulo by zero"); \
		} \
		if (a < 0) { \
			return -((-a) % (b < 0 ? -b : b)); \
		} else { \
			return a % (b < 0 ? -b : b); \
		} \
	}
// This is for types that C doesn't implement % for -- i.e. reals.
// (The cgtests want to do \ with REAL32 and REAL64, although I've never seen it
// in a real program.)
#define MAKE_DUMB_REM(type) \
	static inline type occam_rem_##type (type, type, const char *) occam_unused; \
	static inline type occam_rem_##type (type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, "modulo by zero"); \
		} \
		type i = trunc (a / b); \
		return a - (i * b); \
	}

#define MAKE_ALL_SIGNED(type,flag) \
	MAKE_RANGE_CHECK(type,flag) \
	MAKE_ADD(type) \
	MAKE_SUBTR(type) \
	MAKE_MUL(type) \
	MAKE_DIV(type) \
	MAKE_REM(type) \
	MAKE_NEGATE(type)

//{{{ uint8_t
MAKE_RANGE_CHECK(uint8_t, "%d")
MAKE_ADD(uint8_t)
MAKE_SUBTR(uint8_t)
MAKE_MUL(uint8_t)
MAKE_DIV(uint8_t)

// occam's only unsigned type, so we can use % directly.
static inline uint8_t occam_rem_uint8_t (uint8_t, uint8_t, const char *) occam_unused;
static inline uint8_t occam_rem_uint8_t (uint8_t a, uint8_t b, const char *pos) {
	if (b == 0) {
		occam_stop (pos, "modulo by zero");
	}
	return a % b;
}

// we don't define negate for unsigned types 

//}}}
//{{{ int16_t
MAKE_ALL_SIGNED(int16_t, "%d")
//}}}
//{{{ int
MAKE_ALL_SIGNED(int, "%d")
//}}}
//{{{ int32_t
MAKE_ALL_SIGNED(int32_t, "%d")
//}}}
//{{{ int64_t
MAKE_ALL_SIGNED(int64_t, "%lld")
//}}}
// FIXME range checks for float and double shouldn't work this way
//{{{ float
MAKE_RANGE_CHECK(float, "%f")
MAKE_ADD(float)
MAKE_SUBTR(float)
MAKE_MUL(float)
MAKE_DIV(float)
MAKE_NEGATE(float)
MAKE_DUMB_REM(float)
//}}}
//{{{ double
MAKE_RANGE_CHECK(double, "%f")
MAKE_ADD(double)
MAKE_SUBTR(double)
MAKE_MUL(double)
MAKE_DIV(double)
MAKE_NEGATE(double)
MAKE_DUMB_REM(double)
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
	return (int64_t) roundf (v);
}

int64_t occam_convert_float_int64_t_trunc (float, const char *) occam_unused;
int64_t occam_convert_float_int64_t_trunc (float v, const char *pos) {
	return (int64_t) truncf (v);
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
	return (int64_t) round (v);
}

int64_t occam_convert_double_int64_t_trunc (double, const char *) occam_unused;
int64_t occam_convert_double_int64_t_trunc (double v, const char *pos) {
	return (int64_t) trunc (v);
}
//}}}
//}}}

//{{{ intrinsics
// FIXME These should do range checks.

static inline float occam_SQRT (float, const char *) occam_unused;
static inline float occam_SQRT (float v, const char *pos) {
	return sqrtf (v);
}

static inline double occam_DSQRT (double, const char *) occam_unused;
static inline double occam_DSQRT (double v, const char *pos) {
	return sqrt (v);
}
//}}}

//{{{ lists

#define DECLARE_LIST_TYPE(type, name) struct name { struct name * next; type data; }; \
	name * array_to_list_##name (const type * _array, const int _size) { \
		if (_size <= 0) return NULL; name * r = (name *)malloc(sizeof(name)); \
		r->next = NULL; r->data = _array[0]; name * p = r; \
		for (int i = 1;i < _size;i++) p = append_data_to_list_##name (p,&_array[i]); \
		return r; } \
	name * append_data_to_list_##name (const name * p, const type* data) { \
		p->next = (name *)malloc(sizeof(name));p = p->next; \
		p->next = NULL; p->data = *data; return p; }

//}}}

#endif
