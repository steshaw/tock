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

int main(int argc, char** argv)
{
	int passes = 0;
	int failures = 0;
	
	//Since we test commutativity (at least for 8- and 16-bits),
	//we only need to test one arrangement of each addition
	//and multiplication test
	
	check_addition(127,occam_add_int8_t);
	check_addition(32767,occam_add_int16_t);
	check_addition(2147483647,occam_add_int32_t);
	check_addition(9223372036854775807,occam_add_int64_t);
	
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

	printf("Tests complete, passed: %d, failed: %d\n", passes, failures);
	
	return -failures;
}
