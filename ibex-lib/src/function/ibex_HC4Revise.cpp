//============================================================================
//                                  I B E X                                   
// File        : HC4Revise Algorithm
// Author      : Gilles Chabert
// Copyright   : Ecole des Mines de Nantes (France)
// License     : See the LICENSE file
// Created     : Dec 31, 2011
// Last update : Jan 28, 2020
//============================================================================

#include "ibex_Function.h"
#include "ibex_HC4Revise.h"
#include "ibex_ArbInterface.h"

#include <vector>
#include <stack>
#include <chrono>
#include <string>

namespace ibex {

bool constrain_prune;
double max_prune_width;

// stupid way of getting constants dynamically from environment at runtime.
std::string getEnvVar(const std::string & key) {
    char * val = getenv( key.c_str() );
    return val == NULL ? std::string("") : std::string(val);
}

#define PREC 32

HC4Revise::HC4Revise(Eval& e) : f(e.f), eval(e), d(e.d) {
	// Default integral initialization
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

	std::string threshold = getEnvVar("MAX_PRUNE_WIDTH");
	if (threshold == "") {
		constrain_prune = false;
	} else {
		constrain_prune = true;
		max_prune_width = std::stod(threshold);
	}
}

bool HC4Revise::proj(const Domain& y, Array<Domain>& x) {
	eval.eval(x);

	bool is_inner=backward(y);

	d.read_arg_domains(x);

	return is_inner;
//	return proj(y,(const Array<const Domain>&) x);
}

//bool HC4Revise::proj(const Domain& y, const Array<const Domain>& x) {
//}

bool HC4Revise::proj(const Domain& y, IntervalVector& x) {
	eval.eval(x);
	//std::cout << "forward:" << std::endl; f.cf.print(d);

	bool is_inner=false;

	try {
		is_inner = backward(y);

		d.read_arg_domains(x);

		return is_inner;

	} catch(EmptyBoxException&) {
		x.set_empty();
		return false;
	}
}

bool HC4Revise::backward(const Domain& y) {

	Domain& root=*d.top;

	// note: we can't just return "true" if the domain of the root
	// is a subset of y, because the domains of variables may also
	// be outside of the definition domain of the function.
	// See issue #431.

	root &= y;

	if (root.is_empty())
		throw EmptyBoxException();

	// may throw an EmptyBoxException().
	eval.f.backward<HC4Revise>(*this);

	return false;
	//std::cout << "backward:" << std::endl; f.cf.print();
}

void HC4Revise::idx_cp_bwd(int x, int y) {
	assert(dynamic_cast<const ExprIndex*> (&f.node(y)));

	const ExprIndex& e = (const ExprIndex&) f.node(y);

	d[x].put(e.index.first_row(), e.index.first_col(), d[y]);
}

void HC4Revise::apply_bwd(int* x, int y) {
	assert(dynamic_cast<const ExprApply*> (&f.node(y)));

	const ExprApply& a = (const ExprApply&) f.node(y);

	assert(&a.func!=&f); // recursive calls not allowed
	// TODO Cody: This isn't sufficient for
	// preventing errors: it's multiple activations of the same
	// function at the same time that must not be allowed.

	Array<Domain> d2(a.func.nb_arg());

	for (int i=0; i<a.func.nb_arg(); i++) {
		d2.set_ref(i,d[x[i]]);
	}

	// if next instruction throws an EmptyBoxException,
	// it will be caught by proj(...,IntervalVector& x).
	// (it is a protected function, not called outside of the class
	// so there is no risk)
	a.func.hc4revise().proj(d[y],d2);
}

void HC4Revise::vector_bwd(int* x, int y) {
	assert(dynamic_cast<const ExprVector*>(&(f.node(y))));

	const ExprVector& v = (const ExprVector&) f.node(y);

	assert(v.type()!=Dim::SCALAR);

	int j=0;

	if (v.dim.is_vector()) {
		for (int i=0; i<v.length(); i++) {
			if (v.arg(i).dim.is_vector()) {
				if ((d[x[i]].v() &= d[y].v().subvector(j,j+v.arg(i).dim.vec_size()-1)).is_empty())
						throw EmptyBoxException();
				j+=v.arg(i).dim.vec_size();
			} else {
				if ((d[x[i]].i() &= d[y].v()[j]).is_empty())
					throw EmptyBoxException();
				j++;
			}
		}

		assert(j==v.dim.vec_size());
	}
	else {
		if (v.row_vector()) {
			for (int i=0; i<v.length(); i++) {
				if (v.arg(i).dim.is_matrix()) {
					if ((d[x[i]].m()&=d[y].m().submatrix(0,v.dim.nb_rows()-1,j,j+v.arg(i).dim.nb_cols()-1)).is_empty())
						throw EmptyBoxException();
					j+=v.arg(i).dim.nb_cols();
				} else if (v.arg(i).dim.is_vector()) {
					if ((d[x[i]].v()&=d[y].m().col(j)).is_empty())
						throw EmptyBoxException();
					j++;
				}
			}
		} else {
			for (int i=0; i<v.length(); i++) {
				if (v.arg(i).dim.is_matrix()) {
					if ((d[x[i]].m()&=d[y].m().submatrix(j,j+v.arg(i).dim.nb_rows()-1,0,v.dim.nb_cols()-1)).is_empty())
						throw EmptyBoxException();
					j+=v.arg(i).dim.nb_rows();
				} else if (v.arg(i).dim.is_vector()) {
					if ((d[x[i]].v()&=d[y].m().row(j)).is_empty())
						throw EmptyBoxException();
					j++;
				}
			}
		}
	}
}

void HC4Revise::gen2_bwd(int x1, int x2, int y) {
	assert(dynamic_cast<const ExprGenericBinaryOp*>(&(f.node(y))));

	const ExprGenericBinaryOp& e = (const ExprGenericBinaryOp&) f.node(y);
	e.bwd(d[y], d[x1], d[x2]);
	if (d[x1].is_empty() || d[x2].is_empty()) throw EmptyBoxException();
}

void HC4Revise::gen1_bwd(int x, int y) {
	assert(dynamic_cast<const ExprGenericUnaryOp*>(&(f.node(y))));

	const ExprGenericUnaryOp& e = (const ExprGenericUnaryOp&) f.node(y);
	e.bwd(d[y], d[x]);
	if (d[x].is_empty()) throw EmptyBoxException();
}

// TODO: Make more efficient. I was reluctant to do this because 
// I already found a bug in integral_bwd.
Interval HC4Revise::eval_integral(const ExprIntegral& n, const Array<Domain>& d) {
	// Initialize arguments
	vector<acb_t> d2(n.integrand.nb_arg());
	for (int i=0; i<n.integrand.nb_arg(); i++) {
		acb_init(d2[i]);
	}
	for (int i=1; i<n.integrand.nb_arg(); i++) {
		acb_set_interval(d2[i], d[i + 1].i());
	}

	ComplexIntegrandArgs args;
	args.n = &n;
	args.d2 = &d2;

	acb_t res, a, b;
	acb_init(res);
	acb_init(a);
	acb_init(b);

	// Initialize endpoints and result variables
	acb_zero(res);
	acb_set_interval(a, d[0].i());
	acb_set_interval(b, d[1].i());

	acb_calc_integrate(
		res, 
		&arb_complex_integrand, 
		(void*) &args, 
		a, b,
		integral_goal, 
		integral_tol,
		integral_options,
		integral_prec
	);

	Interval i_res = acb_get_interval(res);

	acb_clear(res);
	acb_clear(a);
	acb_clear(b);

	for (int i=0; i<n.integrand.nb_arg(); i++) {
		acb_clear(d2[i]);
	}

	return i_res;
}

void HC4Revise::integral_bwd(int* x, int y) {
	assert(dynamic_cast<const ExprIntegral*> (&f.node(y)));

	const ExprIntegral& n = (const ExprIntegral&) f.node(y);

	assert(&n.integrand!=&f); // recursive calls not allowed
	// TODO Cody: This isn't sufficient for
	// preventing errors: it's multiple activations of the same
	// function at the same time that must not be allowed.

	Array<Domain> d2(n.nb_args);
	std::vector<Interval> i2(n.nb_args);

	for (int i=0; i<n.nb_args; i++) {
		d2.set_ref(i,d[x[i]]);
	}

	bool taint = false;

	if (constrain_prune) {
		for (int i=0; i<n.nb_args; i++) {
			if (d2[i].i().diam() >= max_prune_width) {
				taint = true;
				break;
			}
		}
	}

	for (int i=0; i<n.nb_args; i++) {
		Interval old_i = d2[i].i();
		Interval new_i;

		// Trivial case: if empty, just pass it forward.
		if (old_i.diam() <= 0 || taint) {
			new_i = old_i;
		} else {
			// experiment with this.
			double threshold = integral_eps;

			// Bisection method.
			Interval lb_i, ub_i;

			// Stack of shrinking intervals
			std::stack<Interval> stack_i;
			bool done;

			// Find lower bound.
			done = false;
			stack_i.push(old_i);
			while (!stack_i.empty() && !done) {
				Interval cur_i = stack_i.top();

				d2[i].i() = cur_i;
				Interval res = eval_integral(n, d2);
				if (d[y].i().overlaps(res)) {
					if (cur_i.diam() <= threshold) {
						done = true;
					} else {
						Interval next_i = Interval(cur_i.lb(), cur_i.mid());
						stack_i.push(next_i);
					}
				} else {
					stack_i.pop();
					if (stack_i.empty()) {
						new_i = Interval::empty_set();
						goto postlude;
					}
					cur_i = stack_i.top();
					cur_i = Interval(cur_i.mid(), cur_i.ub());
					stack_i.pop();
					stack_i.push(cur_i);
					done = true;
				}
			}
			
			// Install lower bound
			if (stack_i.empty()) {
				new_i = old_i;
				goto postlude;
			}
			lb_i = stack_i.top();
			
			// clear stack
			stack_i = {};

			// Find upper bound.
			done = false;
			stack_i.push(old_i);
			while (!stack_i.empty() && !done) {
				Interval cur_i = stack_i.top();

				d2[i].i() = cur_i;
				Interval res = eval_integral(n, d2);
				if (d[y].i().overlaps(res)) {
					if (cur_i.diam() <= threshold) {
						done = true;
					} else {
						Interval next_i = Interval(cur_i.mid(), cur_i.ub());
						stack_i.push(next_i);
					}
				} else {
					stack_i.pop();
					if (stack_i.empty()) {
						new_i = Interval::empty_set();
						goto postlude;
					}
					cur_i = stack_i.top();
					cur_i = Interval(cur_i.lb(), cur_i.mid());
					stack_i.pop();
					stack_i.push(cur_i);
					done = true;
				}
			}
			
			// Install upper bound
			if (stack_i.empty()) {
				new_i = old_i;
				goto postlude;
			}
			ub_i = stack_i.top();

			// OLD WAY OF DOING THINGS....

			// // Find lower bound.
			// done = false;
			// fail = false;
			// stack_i.push(old_i);
			// while (!stack_i.empty() && !done) {
			// 	Interval cur_i = stack_i.top();
			// 	if (fail) {
			// 		cur_i = Interval(cur_i.mid(), cur_i.ub());
			// 		stack_i.pop();
			// 		stack_i.push(cur_i);
			// 		fail = false;
			// 	}

			// 	d2[i].i() = cur_i;
			// 	Interval res = eval_integral(n, d2);
			// 	if (d[y].i().overlaps(res)) {
			// 		if (cur_i.diam() <= threshold) {
			// 			done = true;
			// 		} else {
			// 			Interval next_i = Interval(cur_i.lb(), cur_i.mid());
			// 			stack_i.push(next_i);
			// 		}
			// 	} else {
			// 		stack_i.pop();
			// 		fail = true;
			// 	}
			// }
			
			// // Install lower bound
			// if (stack_i.empty()) {
			// 	new_i = old_i;
			// 	goto postlude;
			// }
			// lb_i = stack_i.top();
			
			// // clear stack
			// stack_i = {};

			// // Find upper bound.
			// done = false;
			// fail = false;
			// stack_i.push(old_i);
			// while (!stack_i.empty() && !done) {
			// 	Interval cur_i = stack_i.top();
			// 	if (fail) {
			// 		cur_i = Interval(cur_i.lb(), cur_i.mid());
			// 		stack_i.pop();
			// 		stack_i.push(cur_i);
			// 		fail = false;
			// 	}

			// 	d2[i].i() = cur_i;
			// 	Interval res = eval_integral(n, d2);
			// 	if (d[y].i().overlaps(res)) {
			// 		if (cur_i.diam() <= threshold) {
			// 			done = true;
			// 		} else {
			// 			Interval next_i = Interval(cur_i.mid(), cur_i.ub());
			// 			stack_i.push(next_i);
			// 		}
			// 	} else {
			// 		stack_i.pop();
			// 		fail = true;
			// 	}
			// }
			
			// // Install upper bound
			// if (stack_i.empty()) {
			// 	new_i = old_i;
			// 	goto postlude;
			// }
			// ub_i = stack_i.top();

			new_i = Interval(lb_i.lb(), ub_i.ub());
		}

postlude:
		d2[i].i() = old_i;

		if (new_i.is_empty())
			throw EmptyBoxException();
		
		i2[i] = new_i;
	}

	for (int i=0; i<n.nb_args; i++) {
		d[x[i]].i() = i2[i];
	}
}

} /* namespace ibex */
