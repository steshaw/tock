/*
 * C99/C++ common support code for Tock programs
 * Copyright (C) 2007, 2008  University of Kent
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
#include <fenv.h>
#include <float.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>
#include <stdlib.h>


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

#ifdef INT
#define tock_old_INT INT
#endif
#ifdef UINT
#define tock_old_UINT UINT
#endif
#ifdef OCCAM_BOOL
#define tock_old_OCCAM_BOOL OCCAM_BOOL
#endif
#ifdef REAL
#define tock_old_REAL REAL
#endif
#ifdef RINT
#define tock_old_RINT RINT
#endif

//We use #define so we can #undef afterwards
#if occam_INT_size == 4
	#define INT int32_t
	#define UINT uint32_t
#elif occam_INT_size == 8
	#define INT int64_t
	#define UINT uint64_t
#else
	#error You must define occam_INT_size when using this header
#endif

#ifdef __cplusplus
#define OCCAM_BOOL bool
#else
#define OCCAM_BOOL _Bool
#endif


//{{{ runtime check functions
static inline int occam_check_slice (int, int, int, const char *) occam_unused;
static inline int occam_check_slice (int start, int count, int limit, const char *pos) {
	int end = start + count;
	if (count != 0 && (start < 0 || start >= limit
	                   || end < 0 || end > limit
	                   || count < 0)) {
		occam_stop (pos, 4, "invalid array slice from %d to %d (should be 0 <= i <= %d)", start, end, limit);
	}
	return start;
}
static inline int occam_check_index (int, int, const char *) occam_unused;
static inline int occam_check_index (int i, int limit, const char *pos) {
	if (i < 0 || i >= limit) {
		occam_stop (pos, 3, "invalid array index %d (should be 0 <= i < %d)", i, limit);
	}
	return i;
}
static inline int occam_check_index_lower (int, const char *) occam_unused;
static inline int occam_check_index_lower (int i, const char *pos) {
	if (i < 0) {
		occam_stop (pos, 2, "invalid array index %d (should be 0 <= i)", i);
	}
	return i;
}
static inline int occam_check_index_upper (int, int, const char *) occam_unused;
static inline int occam_check_index_upper (int i, int limit, const char *pos) {
	if (i >= limit) {
		occam_stop (pos, 3, "invalid array index %d (should be i < %d)", i, limit);
	}
	return i;
}
static inline int occam_check_retype (int, int, const char *) occam_unused;
static inline int occam_check_retype (int src, int dest, const char *pos) {
	if (src % dest != 0) {
		occam_stop (pos, 3, "invalid size for RETYPES/RESHAPES (%d does not divide into %d)", dest, src);
	}
	return src / dest;
}
//}}}

//{{{ type-specific arithmetic ops and runtime checks
#define MAKE_RANGE_CHECK(type, format) \
	static inline type occam_range_check_##type (type, type, type, const char *) occam_unused; \
	static inline type occam_range_check_##type (type lower, type upper, type n, const char *pos) { \
		if (n < lower || n > upper) { \
			occam_stop (pos, 4, "invalid value in conversion " format " (should be " format " <= i <= " format ")", n, lower, upper); \
		} \
		return n; \
	}
// Some things taken from http://www.fefe.de/intof.html

#define __HALF_MAX_SIGNED(type) ((type)1 << (sizeof(type)*CHAR_BIT-2))
#define __MAX_SIGNED(type) (__HALF_MAX_SIGNED(type) - 1 + __HALF_MAX_SIGNED(type))
#define __MIN_SIGNED(type) (-1 - __MAX_SIGNED(type))

#define __MIN(type) ((type)-1 < 1?__MIN_SIGNED(type):(type)0)
#define __MAX(type) ((type)~__MIN(type))

#define MAKE_ADD(type, otypes, format) \
	static inline type occam_add_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_add_##otypes (occam_extra_param type a, type b, const char *pos) { \
		if (((b<1)&&(__MIN(type)-b<=a)) || ((b>=1)&&(__MAX(type)-b>=a))) {return a + b;} \
		else { occam_stop(pos, 3, "integer overflow when doing " format " + " format, a, b); return 0; } \
	}
#define MAKE_ADDF(type, otypes) \
	static inline type occam_add_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_add_##otypes (occam_extra_param type a, type b, const char *pos) { return a + b;}
#define MAKE_SUBTR(type, otypes, format) \
	static inline type occam_subtr_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_subtr_##otypes (occam_extra_param type a, type b, const char *pos) { \
		if (((b<1)&&(__MAX(type)+b>=a)) || ((b>=1)&&(__MIN(type)+b<=a))) {return a - b;} \
		else { occam_stop(pos, 3, "integer overflow when doing " format " - " format, a, b); } \
	}
#define MAKE_SUBTRF(type, otypes) \
	static inline type occam_subtr_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_subtr_##otypes (occam_extra_param type a, type b, const char *pos) { return a - b;}

#define MAKE_MUL(type, otypes, format) \
	static inline type occam_mul_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_mul_##otypes (occam_extra_param const type a, const type b, const char *pos) { \
		if (sizeof(type) < sizeof(long)) /*should be statically known*/ { \
			const long r = (long)a * (long) b; \
			if (r < (long)__MIN(type) || r > (long)__MAX(type)) { \
				occam_stop(pos, 3, "integer overflow when doing " format " * " format, a, b); \
			} else { \
				return (type)r; \
			} \
		} else { \
			/* Taken from: http://www.mail-archive.com/debian-bugs-dist@lists.debian.org/msg326431.html */ \
        	const type r = a * b; \
   	    	if (b != 0 && r / b != a) { \
       			occam_stop(pos, 3, "integer overflow when doing "format " * " format, a, b); \
       		} else { \
        		return r; \
			} \
        } \
	}

#define MAKE_MULF(type, otypes) \
	static inline type occam_mul_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_mul_##otypes (occam_extra_param type a, type b, const char *pos) { return a * b;}
#define MAKE_DIV(type, otypes) \
	static inline type occam_div_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_div_##otypes (occam_extra_param type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, 1, "divide by zero"); \
		} \
		else if (b == -1 && a == __MIN(type)) /* only overflow I can think of */ { \
			occam_stop (pos, 1, "overflow in division"); \
		} else { return a / b; } \
	}
#define MAKE_DIVF(type, otypes) \
	static inline type occam_div_##type (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_div_##type (occam_extra_param type a, type b, const char *pos) { return a / b;}
#define MAKE_NEGATE(type, otype) \
	static inline type occam_subtr_##otype (occam_extra_param type, const char *) occam_unused; \
	static inline type occam_subtr_##otype (occam_extra_param type a, const char *pos) { \
		if (a == __MIN(type)) { \
			occam_stop (pos, 1, "overflow in negation"); \
		} else {return - a;} \
	}
#define MAKE_NEGATEF(type, otype) \
	static inline type occam_negate_##otype (occam_extra_param type, const char *) occam_unused; \
	static inline type occam_negate_##otype (occam_extra_param type a, const char *pos) { return - a; }

// occam's \ doesn't behave like C's %; it handles negative arguments.
// (Effectively it ignores signs coming in, and the output sign is the sign of
// the first argument.)
#define MAKE_REM(type, otypes) \
	static inline type occam_rem_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_rem_##otypes (occam_extra_param type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, 1, "modulo by zero"); \
		} else if (a == __MIN(type)) { \
			return a % (b < 0 ? -b : b); \
		} else if (a < 0) { \
			return -((-a) % (b < 0 ? -b : b)); \
		} else { \
			return a % (b < 0 ? -b : b); \
		} \
	}
// This is for types that C doesn't implement % for -- i.e. reals.
// (The cgtests want to do \ with REAL32 and REAL64, although I've never seen it
// in a real program.)
#define MAKE_DUMB_REM(type, otypes) \
	static inline type occam_rem_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_rem_##otypes (occam_extra_param type a, type b, const char *pos) { \
		if (b == 0) { \
			occam_stop (pos, 1, "modulo by zero"); \
		} \
		type i = round (a / b); \
		return a - (i * b); \
	}

#define MAKE_SHIFT(utype, type, otypes) \
	static inline type occam_lshift_##otypes (occam_extra_param type, int, const char*) occam_unused; \
	static inline type occam_lshift_##otypes (occam_extra_param type a, int b, const char* pos) { \
		if (b < 0 || b > (int)(sizeof(type) * CHAR_BIT)) { \
			occam_stop (pos, 1, "left shift by negative value or value (strictly) greater than number of bits in type"); \
		} else if (b == (int)(sizeof(type) * CHAR_BIT)) { \
			return 0; \
		} else { \
			return (a << b); \
		} \
	} \
	static inline type occam_rshift_##otypes (occam_extra_param type, int, const char*) occam_unused; \
	static inline type occam_rshift_##otypes (occam_extra_param type a, int b, const char* pos) { \
		if (b < 0 || b > (int)(sizeof(type) * CHAR_BIT)) { \
			occam_stop (pos, 1, "right shift by negative value or value (strictly) greater than number of bits in type"); \
		} else if (b == (int)(sizeof(type) * CHAR_BIT)) { \
			return 0; \
		} else { \
			return (type)(((utype)a) >> b); \
		} \
	}

// The main purpose of these three - since they don't need to check for overflow -
// is to constrain the types of the results to prevent unexpected integer promotions
#define MAKE_PLUS(type, otypes) \
	static inline type occam_plus_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_plus_##otypes (occam_extra_param type a, type b, const char *pos) { \
		return a + b; \
	}
#define MAKE_MINUS(type, otypes) \
	static inline type occam_minus_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_minus_##otypes (occam_extra_param type a, type b, const char *pos) { \
		return a - b; \
	}
#define MAKE_TIMES(type, otypes) \
	static inline type occam_times_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_times_##otypes (occam_extra_param type a, type b, const char *pos) { \
		return a * b; \
	}

#define MAKE_SIMPLE_COMP(name, op, type, otypes) \
	static inline OCCAM_BOOL occam_##name##_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline OCCAM_BOOL occam_##name##_##otypes (occam_extra_param type a, type b, const char *pos) { \
		return a op b; \
	}

#define MAKE_ALL_COMP(type, otypes) \
	MAKE_SIMPLE_COMP(less,<,type,otypes) \
	MAKE_SIMPLE_COMP(more,>,type,otypes) \
	MAKE_SIMPLE_COMP(lessEq,<=,type,otypes) \
	MAKE_SIMPLE_COMP(moreEq,>=,type,otypes) \
	MAKE_SIMPLE_COMP(eq,==,type,otypes) \
	MAKE_SIMPLE_COMP(notEq,!=,type,otypes)

#define MAKE_SIMPLE(name, op, type, otypes) \
	static inline type occam_##name##_##otypes (occam_extra_param type, type, const char *) occam_unused; \
	static inline type occam_##name##_##otypes (occam_extra_param type a, type b, const char *pos) { \
		return a op b; \
	}

#define MAKE_ALL_BITWISE(type, otypes) \
	MAKE_SIMPLE(and,&,type,otypes) \
	MAKE_SIMPLE(or,|,type,otypes) \

#define MAKE_TOSTRING(type, occname, flag) \
	static inline void occam_##occname##TOSTRING(INT*, unsigned char*, const type) occam_unused; \
	static inline void occam_##occname##TOSTRING(INT* len, unsigned char* string, const type n) { \
		/* Must use buffer to avoid writing trailing zero: */ char buf[32]; \
		int chars_written = snprintf(buf, 32, flag, n); \
		memcpy(string, buf, chars_written * sizeof(char)); \
		*len = chars_written; \
	}

#define MAKE_STRINGTO(type, occname, flag) \
	static inline void occam_STRINGTO##occname(occam_extra_param OCCAM_BOOL*, type*, const unsigned char*) occam_unused; \
	static inline void occam_STRINGTO##occname(occam_extra_param OCCAM_BOOL* error, type* n, const unsigned char* string) { \
	  *error = 1 != sscanf((const char*)string, flag, n);			\
	}

#define MAKE_STRINGTO_SMALL(type, occname, flag) \
	static inline void occam_STRINGTO##occname(occam_extra_param OCCAM_BOOL*, type*, const unsigned char*) occam_unused; \
	static inline void occam_STRINGTO##occname(occam_extra_param OCCAM_BOOL* error, type* n, const unsigned char* string) { \
			int t; \
			*error = 1 != sscanf((const char*)string, flag, &t) || (int)(type)t != t; \
			*n = (type)t; \
	}

//Same arrangement regardless of our processor size:
#define MAKE_STRINGTO_8 MAKE_STRINGTO_SMALL
#define MAKE_STRINGTO_16 MAKE_STRINGTO_SMALL
#define MAKE_STRINGTO_32 MAKE_STRINGTO
#define MAKE_STRINGTO_64 MAKE_STRINGTO

static inline void occam_BOOLTOSTRING(occam_extra_param INT*, unsigned char*, const OCCAM_BOOL) occam_unused;
static inline void occam_BOOLTOSTRING(occam_extra_param INT* len, unsigned char* str, const OCCAM_BOOL b) {
	if (b) {
		memcpy(str,"TRUE",4*sizeof(char));
		*len = 4;
	} else {
		memcpy(str,"FALSE",5*sizeof(char));
		*len = 5;
	}
}

static inline void occam_STRINGTOBOOL(occam_extra_param OCCAM_BOOL*, OCCAM_BOOL*, const unsigned char*) occam_unused;
static inline void occam_STRINGTOBOOL(occam_extra_param OCCAM_BOOL* error, OCCAM_BOOL* b, const unsigned char* str) {
	if (memcmp("TRUE", str, 4*sizeof(char)) == 0) {
		*b = true;
		*error = false;
	} else if (memcmp("FALSE", str, 5*sizeof(char)) == 0) {
		*b = false;
		*error = false;
	} else {
		*error = true;
	}
}


#define MAKE_ALL_SIGNED(type,bits,flag,hflag,utype,otype) \
	MAKE_RANGE_CHECK(type,flag) \
	MAKE_ADD(type,otype##_##otype,flag) \
	MAKE_SUBTR(type,otype##_##otype,flag) \
	MAKE_MUL(type,otype##_##otype,flag) \
	MAKE_DIV(type,otype##_##otype) \
	MAKE_REM(type,otype##_##otype) \
	MAKE_NEGATE(type,otype) \
	MAKE_SHIFT(utype, type,otype##_##otype) \
	MAKE_PLUS(type,otype##_##otype) \
	MAKE_MINUS(type,otype##_##otype) \
	MAKE_TIMES(type,otype##_##otype) \
	MAKE_ALL_BITWISE(type,otype##_##otype) \
	MAKE_ALL_COMP(type,otype##_##otype) \
	MAKE_TOSTRING(type, INT##bits, flag) \
	MAKE_TOSTRING(type, HEX##bits, hflag) \
	MAKE_STRINGTO_##bits(type, INT##bits, flag) \
	MAKE_STRINGTO_##bits(type, HEX##bits, hflag)

MAKE_ALL_COMP(OCCAM_BOOL,BOOL_BOOL)

//{{{ uint8_t
MAKE_RANGE_CHECK(uint8_t, "%d")
MAKE_ADD(uint8_t,BYTE_BYTE,"%d")
MAKE_SUBTR(uint8_t,BYTE_BYTE,"%d")
MAKE_MUL(uint8_t,BYTE_BYTE,"%d")
MAKE_DIV(uint8_t,BYTE_BYTE)
MAKE_SHIFT(uint8_t,uint8_t,BYTE_BYTE)
MAKE_PLUS(uint8_t,BYTE_BYTE)
MAKE_MINUS(uint8_t,BYTE_BYTE)
MAKE_TIMES(uint8_t,BYTE_BYTE)

// occam's only unsigned type, so we can use % directly.
static inline uint8_t occam_rem_BYTE_BYTE (uint8_t, uint8_t, const char *) occam_unused;
static inline uint8_t occam_rem_BYTE_BYTE (uint8_t a, uint8_t b, const char *pos) {
	if (b == 0) {
		occam_stop (pos, 1, "modulo by zero");
	}
	return a % b;
}

// we don't define negate for unsigned types 

//}}}

//{{{ int8_t
MAKE_ALL_SIGNED(int8_t, 8, "%d", "%x", uint8_t, INT8)
//}}}
//{{{ int16_t
MAKE_ALL_SIGNED(int16_t, 16, "%d", "%x", uint16_t, INT16)
//}}}
//{{{ int
//MAKE_ALL_SIGNED(int, "%d", unsigned int)

MAKE_TOSTRING(INT, INT, "%d")
MAKE_TOSTRING(INT, HEX, "%x")
MAKE_STRINGTO(INT, INT, "%d")
MAKE_STRINGTO(INT, HEX, "%x")

#if occam_INT_size == 4
#define TOCK_TMP_INT int32_t
#define TOCK_TMP_INT_FLAG "%d"
#define TOCK_TMP_UINT uint32_t
#elif occam_INT_size == 8
#define TOCK_TMP_INT int64_t
#define TOCK_TMP_INT_FLAG "%lld"
#define TOCK_TMP_UINT uint64_t
#endif

	MAKE_ADD(TOCK_TMP_INT,INT_INT,TOCK_TMP_INT_FLAG)
	MAKE_SUBTR(TOCK_TMP_INT,INT_INT,TOCK_TMP_INT_FLAG)
	MAKE_MUL(TOCK_TMP_INT,INT_INT,TOCK_TMP_INT_FLAG)
	MAKE_DIV(TOCK_TMP_INT,INT_INT)
	MAKE_REM(TOCK_TMP_INT,INT_INT)
	MAKE_NEGATE(TOCK_TMP_INT,INT)
	MAKE_SHIFT(TOCK_TMP_UINT, TOCK_TMP_INT,INT_INT)
	MAKE_PLUS(TOCK_TMP_INT,INT_INT)
	MAKE_MINUS(TOCK_TMP_INT,INT_INT)
	MAKE_TIMES(TOCK_TMP_INT,INT_INT)
	MAKE_ALL_COMP(TOCK_TMP_INT,INT_INT)
	MAKE_ALL_BITWISE(TOCK_TMP_INT,INT_INT)

#undef TOCK_TMP_INT
#undef TOCK_TMP_INT_FLAG
#undef TOCK_TMP_UINT

//}}}
//{{{ int32_t
MAKE_ALL_SIGNED(int32_t,32, "%d", "%x", uint32_t, INT32)
//}}}
//{{{ int64_t
MAKE_ALL_SIGNED(int64_t,64, "%lld", "%llx", uint64_t, INT64)
//}}}

// FIXME range checks for float and double shouldn't work this way
//{{{ float
MAKE_RANGE_CHECK(float, "%f")
MAKE_ADDF(float,REAL32_REAL32)
MAKE_SUBTRF(float,REAL32_REAL32)
MAKE_MULF(float,REAL32_REAL32)
MAKE_DIVF(float,REAL32_REAL32)
MAKE_NEGATEF(float,REAL32)
MAKE_DUMB_REM(float,REAL32_REAL32)
//}}}
//{{{ double
MAKE_RANGE_CHECK(double, "%f")
MAKE_ADDF(double,REAL64_REAL64)
MAKE_SUBTRF(double,REAL64_REAL64)
MAKE_MULF(double,REAL64_REAL64)
MAKE_DIVF(double,REAL64_REAL64)
MAKE_NEGATEF(double,REAL64)
MAKE_DUMB_REM(double,REAL64_REAL64)
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
static float occam_convert_int64_t_float_round (int64_t, const char *) occam_unused;
static float occam_convert_int64_t_float_round (int64_t v, const char *pos) {
	return (float) v;
}

static float occam_convert_int64_t_float_trunc (int64_t, const char *) occam_unused;
static float occam_convert_int64_t_float_trunc (int64_t v, const char *pos) {
	return (float) v;
}

static int64_t occam_convert_float_int64_t_round (float, const char *) occam_unused;
static int64_t occam_convert_float_int64_t_round (float v, const char *pos) {
	return (int64_t) roundf (v);
}

static int64_t occam_convert_float_int64_t_trunc (float, const char *) occam_unused;
static int64_t occam_convert_float_int64_t_trunc (float v, const char *pos) {
	return (int64_t) truncf (v);
}

static float occam_convert_double_float_round (double, const char *) occam_unused;
static float occam_convert_double_float_round (double v, const char *pos) {
	return (float) v;
}

static float occam_convert_double_float_trunc (double, const char *) occam_unused;
static float occam_convert_double_float_trunc (double v, const char *pos) {
	return (float) v;
}
//}}}
//{{{ double
static double occam_convert_int64_t_double_round (int64_t, const char *) occam_unused;
static double occam_convert_int64_t_double_round (int64_t v, const char *pos) {
	return (double) v;
}

static double occam_convert_int64_t_double_trunc (int64_t, const char *) occam_unused;
static double occam_convert_int64_t_double_trunc (int64_t v, const char *pos) {
	return (double) v;
}

static int64_t occam_convert_double_int64_t_round (double, const char *) occam_unused;
static int64_t occam_convert_double_int64_t_round (double v, const char *pos) {
	return (int64_t) round (v);
}

static int64_t occam_convert_double_int64_t_trunc (double, const char *) occam_unused;
static int64_t occam_convert_double_int64_t_trunc (double v, const char *pos) {
	return (int64_t) trunc (v);
}
//}}}
//}}}

//{{{ Mobile Stuff


//}}}


//{{{ intrinsics
// FIXME These should do range checks.

#include "tock_intrinsics_arith.h"
#define REAL float
#define RINT int32_t
#define ADD_PREFIX(a) occam_##a
#define F(func) func##f
#define SPLICE_SIZE(a,b) a##32##b
#include "tock_intrinsics_float.h"
#undef REAL
#undef RINT
#undef ADD_PREFIX
#undef SPLICE_SIZE
#undef F
#define REAL double
#define RINT int64_t
#define ADD_PREFIX(a) occam_D##a
#define SPLICE_SIZE(a,b) a##64##b
#define F(func) func
#include "tock_intrinsics_float.h"

#undef INT
#undef UINT
#undef REAL
#undef RINT
#undef ADD_PREFIX
#undef SPLICE_SIZE
#undef F

#ifdef tock_old_INT
#define INT tock_old_INT
#endif
#ifdef tock_old_UINT
#define UINT tock_old_UINT
#endif
#ifdef tock_old_OCCAM_BOOL
#define OCCAM_BOOL tock_old_OCCAM_BOOL
#endif
#ifdef tock_old_REAL
#define REAL tock_old_REAL
#endif
#ifdef tock_old_RINT
#define RINT tock_old_RINT
#endif

//}}}

//{{{ Terminal handling
static bool tock_uses_tty;
static struct termios tock_saved_termios;

static void tock_restore_terminal () occam_unused;
static void tock_restore_terminal ()
{
	//{{{  restore terminal
	if (tock_uses_tty) {
		if (tcsetattr (0, TCSAFLUSH, &tock_saved_termios) != 0) {
			fprintf (stderr, "Tock: tcsetattr failed\n");
			exit (1);
		}

		tock_uses_tty = false;
	}
	//}}}
}

static void tock_configure_terminal (bool) occam_unused;
static void tock_configure_terminal (bool uses_stdin)
{
	//{{{  configure terminal
	tock_uses_tty = uses_stdin && isatty (0);
	if (tock_uses_tty) {
		struct termios term;

		if (tcgetattr (0, &term) != 0) {
			fprintf (stderr, "Tock: tcgetattr failed\n");
			exit (1);
		}
		tock_saved_termios = term;

		// Disable canonicalised input and echoing.
		term.c_lflag &= ~(ICANON | ECHO);
		// Satisfy a read request when one character is available.
		term.c_cc[VMIN] = 1;
		// Block read requests until VMIN characters are available.
		term.c_cc[VTIME] = 0;

		if (tcsetattr (0, TCSANOW, &term) != 0) {
			fprintf (stderr, "Tock: tcsetattr failed\n");
			exit (1);
		}
	}
	//}}}
}


#endif
