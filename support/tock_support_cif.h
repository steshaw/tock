/*
 * CIF support code for Tock programs
 * Copyright (C) 2008  University of Kent
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

#ifndef TOCK_SUPPORT_CIF_H
#define TOCK_SUPPORT_CIF_H

#include <cif.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>

//{{{  occam_stop
#define occam_stop(pos, nargs, format, args...) \
	do { \
		ExternalCallN (fprintf, 3 + nargs, stderr, \
		               "Program stopped at %s: " format "\n", \
		               pos, ##args); \
		SetErr (); \
	} while (0)
//}}}

#include <tock_support.h>

//{{{ channel array initialisation
static inline void tock_init_chan_array (Channel *, Channel **, int) occam_unused;
static inline void tock_init_chan_array (Channel *pointTo, Channel **pointFrom, int count) {
	for (int i = 0; i < count; i++) {
		pointFrom[i] = &(pointTo[i]);
	}
}
//}}}

//{{{  top-level process interface
static void tock_tlp_input_bcall (FILE *in, int *ch) occam_unused;
static void tock_tlp_input_bcall (FILE *in, int *ch) {
	*ch = fgetc (in);
}

static void tock_tlp_input (Workspace wptr) occam_unused;
static void tock_tlp_input (Workspace wptr) {
	Channel *out	= ProcGetParam (wptr, 0, Channel *);
	Channel *kill	= ProcGetParam (wptr, 1, Channel *);
	FILE *in	= ProcGetParam (wptr, 2, FILE *);

	while (true) {
		int ch = -1;
		KillableBlockingCallN (wptr, tock_tlp_input_bcall, kill, 2, in, &ch);
		if (ch == -1) {
			// The call was killed -- exit.
			break;
		}

		ChanOutChar (wptr, out, ch);
	}
}

static void tock_tlp_input_kill (Workspace wptr, Channel *kill) occam_unused;
static void tock_tlp_input_kill (Workspace wptr, Channel *kill) {
	while (true) {
		// If KillBlockingCall returns -1, the call hasn't started yet,
		// so we reschedule and try again. (If tock_tlp_input is
		// blocked on output we should deadlock anyway.)
		if (KillBlockingCall (wptr, kill) != -1)
			break;
		Reschedule (wptr);
	}
}

static void tock_tlp_output (Workspace wptr) occam_unused;
static void tock_tlp_output (Workspace wptr) {
	Channel *in	= ProcGetParam (wptr, 0, Channel *);
	Channel *kill	= ProcGetParam (wptr, 1, Channel *);
	FILE *out	= ProcGetParam (wptr, 2, FILE *);

	while (true) {
		switch (ProcAlt (wptr, in, kill, NULL)) {
			case 0: {
				uint8_t ch;
				ChanIn (wptr, in, &ch, sizeof ch);
				if (ch == 255) { // FLUSH
					fflush (out);
				} else {
					ExternalCallN (fputc, 2, ch, out);
				}

				break;
			}
			case 1: {
				bool b;
				ChanIn (wptr, kill, &b, sizeof b);
				fflush (out);

				return;
			}
		}
	}
}

static void tock_tlp_output_kill (Workspace wptr, Channel *kill) occam_unused;
static void tock_tlp_output_kill (Workspace wptr, Channel *kill) {
	bool b = true;

	ChanOut (wptr, kill, &b, sizeof b);
}
//}}}

//{{{  CCSP startup and terminal handling
static void tock_exit_handler (int status, word core) occam_unused;
static void tock_exit_handler (int status, word core) {
	tock_restore_terminal ();
	ccsp_default_exit_handler (status, core);
}

static void tock_init_ccsp (bool uses_stdin) occam_unused;
static void tock_init_ccsp (bool uses_stdin) {
	ccsp_set_branding ("Tock");

	tock_configure_terminal (uses_stdin);

	if (!ccsp_init ())
		exit (1);

	ccsp_set_exit_handler (tock_exit_handler);
}
//}}}

#endif
