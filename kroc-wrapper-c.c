/*
 * KRoC wrapper to run Tock-generated CIF program
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
