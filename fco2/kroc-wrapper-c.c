/* KRoC wrapper to run Tock-generated CIF program */

#include <cifccsp.h>

extern void tock_main (Process *me, Channel *in, Channel *out, Channel *err);

void _tock_main_init (int *ws) {
	Process *p = ProcAlloc (tock_main, 65536, 3,
	                        (Channel *) ws[1], (Channel *) ws[2], (Channel *) ws[3]);
	*((int *) ws[0]) = (int) p;
}

void _tock_main_free (int *ws) {
	ProcAllocClean ((Process *) ws[0]);
}
