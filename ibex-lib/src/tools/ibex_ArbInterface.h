/* ============================================================================
 * I B E X - Utility functions to convert between Interval and acb_t
 * ============================================================================
 * Copyright   : Ecole des Mines de Nantes (FRANCE)
 * License     : This program can be distributed under the terms of the GNU LGPL.
 *               See the file COPYING.LESSER.
 *
 * Author(s)   : Cody Rivera
 * Created     : May 12, 2023
 * ---------------------------------------------------------------------------- */

#ifndef __IBEX_ARBINTERFACE_H__
#define __IBEX_ARBINTERFACE_H__

#include "ibex_Interval.h"
#include "acb.h"

namespace ibex {

void acb_set_interval(acb_t z, Interval x);
Interval acb_get_interval(const acb_t z);

} // namespace ibex

#endif // __IBEX_ARBINTERFACE_H__
