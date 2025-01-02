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

#include "ibex_ArbInterface.h"

namespace ibex {

#define PREC (2 * (sizeof(double) * 8))

// Sets the real component of z to x,
// and the imagniary to 0r0.
void acb_set_interval(acb_t z, Interval x) {
    arb_ptr rc = acb_realref(z);
    arb_ptr ic = acb_imagref(z);
    arf_t l, u;
    arf_init(l);
    arf_init(u);
    arf_set_d(l, x.lb());
    arf_set_d(u, x.ub());
    arb_set_interval_arf(rc, l, u, PREC);
    arf_clear(l);
    arf_clear(u);
    arb_zero(ic);
}

// Extracts the real component of z into an Interval.
Interval acb_get_interval(const acb_t z) {
    const arb_struct* rc = acb_realref(z);
    arf_t l, u;
    arf_init(l);
    arf_init(u);
    arb_get_lbound_arf(l, rc, PREC);
    arb_get_ubound_arf(u, rc, PREC);
    Interval i(arf_get_d(l, ARF_RND_FLOOR),
               arf_get_d(u, ARF_RND_CEIL));
    arf_clear(l);
    arf_clear(u);
    return i;
}

} // namespace ibex
