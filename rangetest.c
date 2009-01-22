int g_stopped;

#define occam_stop(pos, nargs, format, args...) do { g_stopped = 1; } while (0)

#include "support/tock_support.h"

#define report_failure(msg, args...) { printf(msg, ##args); }

#define testf(call) do { \
	g_stopped = 0; \
	call; \
	if (g_stopped == 1) { \
		passes++; \
	} else { \
		failures++; \
		report_failure(#call " failed, expected to stop\n"); \
	} \
  } while(0)

#define testp(exp, call) do { \
	g_stopped = 0; \
	if (exp == call) { \
		if (g_stopped == 0) { \
			passes++; \
		} else { \
  			failures++; \
  			report_failure(#call "failed, unexpectedly stopped\n"); \
  		} \
  	} else { \
  		failures++; \
  		if (g_stopped == 1) { \
  			report_failure(#call "failed, unexpectedly stopped\n"); \
		} else { \
  			report_failure(#call " failed, expected %lld, got %lld\n", (int64_t)exp, (int64_t)call); \
  		} \
  	} \
  } while (0)

#define test_commutative(t,f) \
	do {int done_x = 0; for (t x = 0; !(x == 0 && done_x == 1);x+=1) { done_x = 1;\
		int done_y = 0; for (t y = 0; !(y == x && done_y == 1);y+=1) { done_y = 1;\
			g_stopped = 0; \
			const t r0 = f(x,y,""); \
			const int stopped_earlier = g_stopped; \
			g_stopped = 0; \
			const t r1 = f(y,x,""); \
			const int stopped_later = g_stopped; \
			if ((stopped_later == 1 && stopped_earlier == 1) || \
			  (stopped_earlier == 0 && stopped_later == 0 && r0 == r1)) { \
				\
			} else { \
				failures++; \
				report_failure(#f " failed, non-commutative with %d, %d (stop: %d, %d) (res: %d, %d)\n", \
				  (int)x, (int)y, stopped_earlier, stopped_later, r0, r1); \
				goto comm_label_##f; \
			} \
		} \
	}passes++; comm_label_##f:;} while (0)

// All the addition cases I wrote were effectively the same,
// so I just made it a macro.  We define min to be -max-1, which gets around
// the fact that the C standard apparently says that the largest
// constant for a value is -max (not -max-1).
#define check_addition(max, f) \
	do { testp(2,f(1,1,"")); \
		testp(0,f(0,0,"")); \
		testp(-1,f(0,-1,"")); \
		testp(max,f((max>>1)+1,max>>1,"")); \
		testf(f((max>>1)+1,(max>>1)+1,"")); \
		testf(f(max,max,"")); \
		testf(f(-max-1,-max-1,"")); \
		testp(-1,f(-max-1,max,"")); \
		testp(-max-1,f(-max-1,0,"")); \
		testp(max,f(max,0,"")); \
	} while (0)

#define check_subtraction(max, f) \
	do { testp(0,f(1,1,"")); \
		testp(0,f(0,0,"")); \
		testp(0,f(max,max,"")); \
		testp(0,f(-max-1,-max-1,"")); \
		testp(1,f(0,-1,"")); \
		testp(-1,f(0,1,"")); \
		testp(-max,f(0,max,"")); \
		testp(-max-1,f(-1,max,"")); \
		testf(f(-2,max,"")); \
		testp(max,f(0,-max,"")); \
		testp(max,f(1,1-max,"")); \
		testf(f(0,-max-1,"")); \
		testf(f(1,-max,"")); \
	} while (0)

#define check_negation(max, f) \
	do { testp(0,f(0,"")); \
		testp(1,f(-1,"")); \
		testp(-1,f(1,"")); \
		testp(max,f(-max,"")); \
		testp(-max,f(max,"")); \
		testf(f(-max-1,"")); \
	} while (0)

#define check_division(max, f) \
	do { testp(0,f(0,1,"")); \
		testp(0,f(0,-1,"")); \
		testf(f(0,0,"")); \
		testf(f(1,0,"")); \
		testf(f(-1,0,"")); \
		testf(f(max,0,"")); \
		testf(f(-max-1,0,"")); \
		testf(f(-max-1,-1,"")); \
		testp(-max-1,f(-max-1,1,"")); \
		testp(max,f(-max,-1,"")); \
		testp(-max,f(max,-1,"")); \
		testp(max,f(max,1,"")); \
	} while (0)

#define check_rem(max, f) \
	do { testp(0, f(1,1,"")); \
		testp(0, f(0,1,"")); \
		testp(0, f(0,-1,"")); \
		testf(f(0,0,"")); \
		testf(f(1,0,"")); \
		testf(f(-1,0,"")); \
		testf(f(max,0,"")); \
		testf(f(-max-1,0,"")); \
		testp(0,f(max,max,"")); \
		testp(0,f(-max-1,-max-1,"")); \
		testp(-2,f(-max-1,max>>1,"")); \
		testp(-2,f(-max-1,-(max>>1),"")); \
		testp(-1,f(-max,max>>1,"")); \
		testp(-1,f(-max,-(max>>1),"")); \
		testp(-1,f(-max-1,-max,"")); \
		testp(-1,f(-max-1,max,"")); \
		testp(3,f(3,-max-1,"")); \
		testp(-3,f(-3,-max-1,"")); \
		testp(max,f(max,-max-1,"")); \
		testp(-max,f(-max,-max-1,"")); \
	} while (0)

#define check_shift(max,bits,f) \
	do { testp(0, f(0,0,"")); \
		testp(max, f(max,0,"")); \
		testp(-max, f(-max,0,"")); \
		testp(-max-1, f(-max-1,0,"")); \
		testp(1,f(1,0,"")); \
		testp(-1,f(-1,0,"")); \
		testp(0, f(0,bits,"")); \
		testp(0, f(max,bits,"")); \
		testp(0, f(-max,bits,"")); \
		testp(0, f(-max-1,bits,"")); \
		testp(0, f(1,bits,"")); \
		testp(0, f(-1,bits,"")); \
		testf(f(0,-1,"")); \
		testf(f(1,-1,"")); \
		testf(f(-1,-1,"")); \
		testf(f(max,-1,"")); \
		testf(f(-max-1,-1,"")); \
		testf(f(0,bits+1,"")); \
		testf(f(1,bits+1,"")); \
		testf(f(-1,bits+1,"")); \
		testf(f(max,bits+1,"")); \
		testf(f(-max-1,bits+1,"")); \
	} while (0)

#define check_all_b(max,bits,type) \
	check_addition(max,occam_add_##type); \
	check_subtraction(max,occam_subtr_##type); \
	check_negation(max,occam_negate_##type); \
	check_division(max,occam_div_##type); \
	check_rem(max,occam_rem_##type); \
	check_shift(max,bits,occam_lshift_##type); \
	check_shift(max,bits,occam_rshift_##type);

#define check_all(max,bits) check_all_b(max,bits,int##bits##_t)


// The values of various operations (REM, shifts and so on)
// are checked by the cgtest.  All we are concerned with
// testing here is that the various occam support functions
// STOP when they are supposed to, which is something that
// the cgtests do not check.  But it can't hurt that we check
// the various corner cases at the same time.

int main(int argc, char** argv)
{
	int passes = 0;
	int failures = 0;
	
	//Since we test commutativity (at least for 8- and 16-bits),
	//we only need to test one arrangement of each addition
	//and multiplication test
	
	check_all(127,8);
	check_all(32767,16);
	check_all(2147483647,32);
	check_all(9223372036854775807,64);
	
	testf(occam_mul_int8_t(127,127,""));
	testf(occam_mul_int8_t(2,127,""));
	testf(occam_mul_int8_t(127,127,""));
	testf(occam_mul_int8_t(127,-128,""));
	testf(occam_mul_int8_t(-128,-128,""));
	testf(occam_mul_int8_t(-1,-128,""));
	testp(-128,occam_mul_int8_t(1,-128,""));

	
	test_commutative(int8_t,occam_add_int8_t);
	test_commutative(int8_t,occam_mul_int8_t);

	test_commutative(int16_t,occam_add_int16_t);
	test_commutative(int16_t,occam_mul_int16_t);

	//TODO test uint8_t as well
	
	//TODO add tests for the index-checking functions too

	printf("Tests complete, passed: %d, failed: %d\n", passes, failures);
	
	return -failures;
}
