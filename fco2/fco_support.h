/* C99 support definitions for FCO. */

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
#else
#warning No PACKED implementation for this compiler
#endif

static void occam_stop (const char *pos, const char *message) {
	EXTERNAL_CALLN (fprintf, stderr, "Program stopped at %s: %s\n", pos, message);
	SetErr ();
}

/* FIXME All of these need to check for overflow and report errors appropriately. */
static int occam_add (int a, int b, const char *pos) {
	return a + b;
}
static int occam_subtr (int a, int b, const char *pos) {
	return a - b;
}
static int occam_mul (int a, int b, const char *pos) {
	return a * b;
}
static int occam_div (int a, int b, const char *pos) {
	if (b == 0) {
		occam_stop (pos, "divide by zero");
	}
	return a / b;
}
static int occam_rem (int a, int b, const char *pos) {
	if (b == 0) {
		occam_stop (pos, "modulo by zero");
	}
	return a % b;
}
#define occam_after (a, b, pos) \
	(((a) - (b)) > 0)

#endif
