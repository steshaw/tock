/* KRoC wrapper to run FCO-generated CIF program */

#include <cifccsp.h>

extern void fco_main (Process *me, Channel *in, Channel *out, Channel *err);

void _fco_main_init (int *ws) {
	Process *p = ProcAlloc (fco_main, 65536, 3,
	                        (Channel *) ws[1], (Channel *) ws[2], (Channel *) ws[3]);
	*((int *) ws[0]) = (int) p;
}

void _fco_main_free (int *ws) {
	ProcAllocClean ((Process *) ws[0]);
}
