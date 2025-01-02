/* ============================================================================
 * I B E X - Function basic evaluation
 * ============================================================================
 * Copyright   : IMT Atlantique (FRANCE)
 * License     : This program can be distributed under the terms of the GNU LGPL.
 *               See the file COPYING.LESSER.
 *
 * Author(s)   : Gilles Chabert
 * Created     : Jan 14, 2012
 * Last update : Jul 10, 2019
 * ---------------------------------------------------------------------------- */

#include "ibex_Function.h"
#include "ibex_IntegralEval.h"
#include "ibex_ArbInterface.h"

#include <typeinfo>

using namespace std;

namespace ibex {

#define PREC 32

std::string getEnvVar(const std::string & key);


IntegralEval::IntegralEval(Function& f) : f(f), d(f.nodes.size()), arg_locs(f.nb_arg()) {
	for (acb_t& x: d) {
		acb_init(x);
	}

	for (int i=0; i<f.nb_arg(); i++) {
		arg_locs[i] = f.nodes.rank(f.arg(i));
	}

	std::string precision_str = getEnvVar("ARB_PRECISION");
	if (precision_str == "") {
		integral_prec = PREC;
	} else {
		integral_prec = stoi(precision_str);
	}

	
	integral_goal = integral_prec;
	mag_init(integral_tol);
	mag_set_ui_2exp_si(integral_tol, 1, -integral_prec);
	acb_calc_integrate_opt_init(integral_options);
	integral_eps = 0.01;
}

IntegralEval::~IntegralEval() {
	for (acb_t& x: d) {
		acb_clear(x);
	}
	mag_clear(integral_tol);
}

bool IntegralEval::eval(const vector<acb_t>& d2, acb_ptr res) {
	assert(arg_locs.size()==d2.size());
	const vector<int>& used = f.used_vars;

	if (used.empty())
		for (int s=0; s<f.nb_arg(); s++)
			acb_set(d[arg_locs[s]], d2[s]);
	else {
		int i=0; // iterates over the components of box
		std::vector<int>::const_iterator u=used.begin(); // iterates over the array "used"

		for (int s=0; u!=used.end() && s<d2.size(); s++) {
			if (*u>=i+1) {  // next used component is after this symbol
				i++;
				continue; // skip this symbol
			}

			// else: some components of the current symbol d[s] are used.
			// (i.e. they have to be copied in x).
			if (i==*u) {
				acb_set(d[arg_locs[s]], d2[s]);
				++u; // if used.empty(), u is incremented for nothing
				if (u==used.end()) break;
			}
			i++;
		}
		assert(used.empty() || u==used.end());
	}

	holomorphic = true;
	f.forward<IntegralEval>(*this);
	acb_set(res, d[0]);

	return holomorphic;
}

void IntegralEval::idx_cp_fwd(int x, int y) {
	not_implemented("indexed expressions");
}

void IntegralEval::apply_fwd(int* x, int y) {
	assert(dynamic_cast<const ExprApply*> (&f.node(y)));

	const ExprApply& a = (const ExprApply&) f.node(y);

	assert(&a.func!=&f); // recursive calls not allowed
	// TODO Cody: This isn't sufficient for
	// preventing errors: it's multiple activations of the same
	// function at the same time that must not be allowed.

	vector<acb_t> d2(a.func.nb_arg());
	for (int i=0; i<a.func.nb_arg(); i++) {
		acb_init(d2[i]);
		acb_set(d2[i], d[x[i]]);
	}

	bool holo = a.func.integral_evaluator().eval(d2, d[y]);

	if (!holo)
		holomorphic = false;

	for (int i=0; i<a.func.nb_arg(); i++) {
		acb_clear(d2[i]);
	}
}

void IntegralEval::vector_fwd(int* x, int y) {
	not_implemented("vector expressions");
}

void IntegralEval::gen1_fwd(int x, int y) {
	not_implemented("gen1_fwd unsupported");
}

void IntegralEval::gen2_fwd(int x1, int x2, int y) {
	not_implemented("gen2_fwd unsupported");
}

void IntegralEval::integral_fwd(int* x, int y) {
	assert(dynamic_cast<const ExprIntegral*> (&f.node(y)));

	const ExprIntegral& n = (const ExprIntegral&) f.node(y);

	assert(&n.integrand!=&f); // recursive calls not allowed
	// TODO Cody: This isn't sufficient for
	// preventing errors: it's multiple activations of the same
	// function at the same time that must not be allowed.

	// Initialize arguments
	vector<acb_t> d2(n.integrand.nb_arg());
	for (int i=0; i<n.integrand.nb_arg(); i++) {
		acb_init(d2[i]);
	}
	for (int i=1; i<n.integrand.nb_arg(); i++) {
		acb_set(d2[i], d[x[i + 1]]);
	}

	ComplexIntegrandArgs args;
	args.n = &n;
	args.d2 = &d2;
	args.holomorphic = true;

	// Initialize endpoints and result variables
	//integral_options->verbose = 2; // TODO: Remove debug

	acb_zero(d[y]);
	acb_calc_integrate(
		d[y], 
		&arb_complex_integrand, 
		(void*) &args, 
		d[x[0]], d[x[1]], // a, b respectively.
		integral_goal, 
		integral_tol,
		integral_options,
		integral_prec
	);

	if (!(args.holomorphic)) {
		holomorphic = false;
	}

	for (int i=0; i<n.integrand.nb_arg(); i++) {
		acb_clear(d2[i]);
	}
}

// Integration scaffolding to pass to arb
int arb_complex_integrand(acb_ptr res, const acb_t z, void* param, slong order, slong prec) {
	assert(param != NULL);
	ComplexIntegrandArgs* args = (ComplexIntegrandArgs*) param;
	const ExprIntegral& n = *(args->n);
	std::vector<acb_t>& d2 = *(args->d2);

	if (order > 1)
		flint_abort();

	// cout << "z = ";
	// acb_printn(z, 3.333 * prec, 0);
	// cout << " order = " << order << endl;

	acb_set(d2[0], z);

	bool holo = n.integrand.integral_evaluator().eval(d2, res);

	// cout << "res = ";
	// acb_printn(res, 3.333 * prec, 0);

	if (order == 1 && !holo) {
		// cout << n.integrand << endl;
		// cout << n.integrand.cf << endl;
		// cout << "z = ";
		// acb_printn(z, 3.333 * prec, 0);
		// cout << "res = ";
	    // acb_printn(res, 3.333 * prec, 0);
		// cout << " order = " << order << endl;
		// cout << " nonholomorphic \n";
		acb_indeterminate(res);
	} else if (!holo) {
		args->holomorphic = false;
	}
	// cout << endl;

	return 0;
}

} // namespace ibex
