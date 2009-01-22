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
  			report_failure(#call " failed, expected %d, got %d\n", exp, call); \
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



int main(int argc, char** argv)
{
	int passes = 0;
	int failures = 0;
	
	//Since we test commutativity (at least for 8- and 16-bits),
	//we only need to test one arrangement of each addition
	//and multiplication test
	
	testp(2,occam_add_int8_t(1,1,""));
	testp(127,occam_add_int8_t(64,63,""));
	testf(occam_add_int8_t(64,64,""));
	testp(-1,occam_add_int8_t(127,-128,""));
	testp(-1,occam_add_int8_t(-1,0,""));
	testp(-128,occam_add_int8_t(-128,0,""));

	testf(occam_mul_int8_t(127,127,""));
	testf(occam_mul_int8_t(2,127,""));
	testf(occam_mul_int8_t(127,127,""));
	testf(occam_mul_int8_t(127,-128,""));
	testf(occam_mul_int8_t(-128,-128,""));
	testf(occam_mul_int8_t(-1,-128,""));
	testp(-128,occam_mul_int8_t(1,-128,""));

	
	test_commutative(int8_t,occam_add_int8_t);
	test_commutative(int8_t,occam_mul_int8_t);

	testp(-32768,occam_add_int16_t(-32768,0,""));
	testf(occam_add_int16_t(-1,-32768,""));
	testp(32767,occam_add_int16_t(0,32767,""));
	
	test_commutative(int16_t,occam_add_int16_t);
	test_commutative(int16_t,occam_mul_int16_t);

	//TODO test uint8_t as well

	printf("Tests complete, passed: %d, failed: %d\n", passes, failures);
	
	return -failures;
}
