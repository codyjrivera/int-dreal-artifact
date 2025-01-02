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
#include "ibex_Eval.h"
#include "ibex_IntegralEval.h"
#include "ibex_ArbInterface.h"

#include <typeinfo>

using namespace std;

namespace ibex {

#define PREC 32

bool positive_integrals;

// stupid way of getting constants dynamically from environment at runtime.
std::string getEnvVar(const std::string & key);

Eval::Eval(Function& f) : f(f), d(f), fwd_agenda(NULL), bwd_agenda(NULL), matrix_fwd_agenda(NULL), matrix_bwd_agenda(NULL) {

	Dim dim=f.expr().dim;
	int m=dim.vec_size();

	if (m>1) {
		const ExprVector* vec=dynamic_cast<const ExprVector*>(&f.expr());
		if (vec && (vec->orient==ExprVector::COL || dim.type()==Dim::ROW_VECTOR) && m==vec->nb_args) {
			fwd_agenda = new Agenda*[m];
			bwd_agenda = new Agenda*[m];
			for (int i=0; i<m; i++) {
				bwd_agenda[i] = f.cf.agenda(f.nodes.rank(vec->arg(i)));
				fwd_agenda[i] = new Agenda(*bwd_agenda[i],true); // true<=>swap
			}

			if (dim.is_matrix()) {
				int n=dim.nb_cols();

				// check that the matrix is homogeneous (a matrix of scalar expressions)
				bool homogeneous=true; // by default
				for (int i=0; i<m; i++) {
					const ExprVector* fi=dynamic_cast<const ExprVector*>(&vec->arg(i));
					if (!fi || fi->nb_args<n) {
						homogeneous=false;
						break;
					}
				}

				if (homogeneous) {
					matrix_fwd_agenda = new Agenda**[m];
					matrix_bwd_agenda = new Agenda**[m];
					for (int i=0; i<m; i++) {
						const ExprVector& fi=(const ExprVector&) vec->arg(i);
						matrix_fwd_agenda[i] = new Agenda*[n];
						matrix_bwd_agenda[i] = new Agenda*[n];
						for (int j=0; j<n; j++) {
							matrix_bwd_agenda[i][j] = f.cf.agenda(f.nodes.rank(fi.arg(j)));
							matrix_fwd_agenda[i][j] = new Agenda(*matrix_bwd_agenda[i][j],true); // true<=>swap
						}
					}
				}
			}
		}
	}

	std::string precision_str = getEnvVar("ARB_PRECISION");
	if (precision_str == "") {
		integral_prec = PREC;
	} else {
		integral_prec = stoi(precision_str);
	}

	// cout<<"Integral Prec: "<<integral_prec;

	// Default integral initialization
	
	integral_goal = integral_prec;
	mag_init(integral_tol);
	mag_set_ui_2exp_si(integral_tol, 1, -integral_prec);
	acb_calc_integrate_opt_init(integral_options);
	integral_eps = 0.01;

	std::string query = getEnvVar("POSITIVE_INTEGRALS");
	if (query == "") {
		positive_integrals = false;
	} else {
		positive_integrals = (query == "TRUE" || query == "true" || query == "1");
	}

	// cout<<"\nPositive Integrals:"<<positive_integrals;
}

Eval::~Eval() {
	if (fwd_agenda!=NULL) {
		for (int i=0; i<f.expr().dim.vec_size(); i++) {
			delete fwd_agenda[i];
			delete bwd_agenda[i];
		}
		delete[] fwd_agenda;
		delete[] bwd_agenda;

		if (matrix_fwd_agenda!=NULL) {
			for (int i=0; i<f.expr().dim.nb_rows(); i++) {
				for (int j=0; j<f.expr().dim.nb_cols(); j++) {
					delete matrix_fwd_agenda[i][j];
					delete matrix_bwd_agenda[i][j];
				}
				delete[] matrix_fwd_agenda[i];
				delete[] matrix_bwd_agenda[i];
			}
			delete[] matrix_fwd_agenda;
			delete[] matrix_bwd_agenda;
		}
	}
	mag_clear(integral_tol);
}

Domain& Eval::eval(const Array<const Domain>& d2) {

	d.write_arg_domains(d2);

	//------------- for debug
	//	cout << "Function " << f.name << ", domains before eval:" << endl;
	//	for (int i=0; i<f.nb_arg(); i++) {
	//		cout << "arg[" << i << "]=" << f.arg_domains[i] << endl;
	//	}

	try {
		f.forward<Eval>(*this);
	} catch(EmptyBoxException&) {
		d.top->set_empty();
	}
	return *d.top;
}

Domain& Eval::eval(const Array<Domain>& d2) {

	d.write_arg_domains(d2);

	try {
		f.forward<Eval>(*this);
	} catch(EmptyBoxException&) {
		d.top->set_empty();
	}
	return *d.top;
}

Domain& Eval::eval(const IntervalVector& box) {

	d.write_arg_domains(box);

	try {
		f.forward<Eval>(*this);
	} catch(EmptyBoxException&) {
		d.top->set_empty();
	}
	return *d.top;
}

Domain Eval::eval(const IntervalVector& box, const BitSet& components) {

	Dim dim=d.top->dim;

	if (dim.type()==Dim::SCALAR) return eval(box);

	d.write_arg_domains(box);

	assert(!components.empty());

	int m=components.size();

	Domain res(dim.type()==Dim::ROW_VECTOR ?
			Dim(1,m) : // in the case of a row vector, we select columns
			Dim(m,dim.nb_cols())); // in the other cases we select rows

	if (fwd_agenda==NULL) {

		// The vector of expression is heterogeneous (or the expression is scalar).
		//
		// We might be able in this case to use the DAG but
		// - the algorithm is more complex
		// - we might not benefit from possible symbolic simplification due
		//   to the fact that only specific components are required (there is
		//   no simple "on the fly" simplification as in the case of a vector
		//   of homogeneous expressions)
		// so we resort to the components functions f[i] --> symbolic copy+no DAG :(
		int i=0;
		for (BitSet::const_iterator c=components.begin(); c!=components.end(); ++c) {
			res[i++] = f[c].eval_domain(box);
		}
		assert(i==m);

		return res;
	}

	// merge all the agendas
	Agenda a(f.nodes.size()); // the global agenda initialized with the maximal possible value
	for (BitSet::const_iterator c=components.begin(); c!=components.end(); ++c) {
		a.push(*(fwd_agenda[c]));
	}

	try {
		f.cf.forward<Eval>(*this,a);
		int i=0;
		for (BitSet::const_iterator c=components.begin(); c!=components.end(); ++c) {
			res[i++] = d[bwd_agenda[c]->first()];
		}
	} catch(EmptyBoxException&) {
		d.top->set_empty();
		res.set_empty();
	}

	return res;
}

Domain Eval::eval(const IntervalVector& box, const BitSet& rows, const BitSet& cols) {

	Dim dim=d.top->dim;

	switch (dim.type()) {
	case Dim::SCALAR:     return eval(box);
	case Dim::ROW_VECTOR: return eval(box,cols);
	case Dim::COL_VECTOR: return eval(box,rows);
	default : ;// ok continue
	}

	d.write_arg_domains(box);

	assert(!rows.empty());
	assert(!cols.empty());
	assert(rows.max()<dim.nb_rows());
	assert(cols.max()<dim.nb_cols());

	int m=rows.size();
	int n=cols.size();

	Domain res(Dim(m,n));

	if (matrix_fwd_agenda==NULL) {

		// The vector of expression is heterogeneous (or the expression is scalar).
		//
		// We might be able in this case to use the DAG but
		// - the algorithm is more complex
		// - we might not benefit from possible symbolic simplification due
		//   to the fact that only specific components are required (there is
		//   no simple "on the fly" simplification as in the case of a vector
		//   of homogeneous expressions)
		// so we resort to the components functions f[i] --> symbolic copy+no DAG :(
		int i=0;
		for (BitSet::const_iterator r=rows.begin(); r!=rows.end(); ++r, i++) {
				int j=0;
				for (BitSet::const_iterator c=cols.begin(); c!=cols.end(); ++c, j++) {
					res[i][j] = f[r][c].eval_domain(box);
				}
				assert(j==n);
		}
		assert(i==m);

		return res;
	}

	// merge all the agendas
	Agenda a(f.nodes.size()); // the global agenda initialized with the maximal possible value
	for (BitSet::const_iterator r=rows.begin(); r!=rows.end(); ++r) {
		for (BitSet::const_iterator c=cols.begin(); c!=cols.end(); ++c) {
			a.push(*(matrix_fwd_agenda[r][c]));
		}
	}

	try {
		f.cf.forward<Eval>(*this,a);
		int i=0;
		for (BitSet::const_iterator r=rows.begin(); r!=rows.end(); ++r, i++) {
			int j=0;
			for (BitSet::const_iterator c=cols.begin(); c!=cols.end(); ++c, j++) {
				res[i][j] = d[matrix_bwd_agenda[r][c]->first()];
			}
		}
	} catch(EmptyBoxException&) {
		d.top->set_empty();
		res.set_empty();
	}

	return res;
}

void Eval::idx_cp_fwd(int x, int y) {
	assert(dynamic_cast<const ExprIndex*> (&f.node(y)));

	const ExprIndex& e = (const ExprIndex&) f.node(y);

	d[y] = d[x][e.index];
}

void Eval::apply_fwd(int* x, int y) {
	assert(dynamic_cast<const ExprApply*> (&f.node(y)));

	const ExprApply& a = (const ExprApply&) f.node(y);

	assert(&a.func!=&f); // recursive calls not allowed
	// TODO Cody: This isn't sufficient for
	// preventing errors: it's multiple activations of the same
	// function at the same time that must not be allowed.

	Array<const Domain> d2(a.func.nb_arg());

	for (int i=0; i<a.func.nb_arg(); i++) {
		d2.set_ref(i,d[x[i]]);
	}

	d[y] = a.func.basic_evaluator().eval(d2);
}

void Eval::vector_fwd(int* x, int y) {
	assert(dynamic_cast<const ExprVector*>(&(f.node(y))));

	const ExprVector& v = (const ExprVector&) f.node(y);

	assert(v.type()!=Dim::SCALAR);

	int j=0;

	if (v.dim.is_vector()) {
		for (int i=0; i<v.length(); i++) {
			if (v.arg(i).dim.is_vector()) {
				d[y].v().put(j,d[x[i]].v());
				j+=v.arg(i).dim.vec_size();
			} else {
				d[y].v()[j]=d[x[i]].i();
				j++;
			}
		}

		assert(j==v.dim.vec_size());
	}
	else {
		if (v.row_vector()) {
			for (int i=0; i<v.length(); i++) {
				if (v.arg(i).dim.is_matrix()) {
					d[y].m().put(0,j,d[x[i]].m());
					j+=v.arg(i).dim.nb_cols();
				} else if (v.arg(i).dim.is_vector()) {
					d[y].m().set_col(j,d[x[i]].v());
					j++;
				}
			}
		} else {
			for (int i=0; i<v.length(); i++) {
				if (v.arg(i).dim.is_matrix()) {
					d[y].m().put(j,0,d[x[i]].m());
					j+=v.arg(i).dim.nb_rows();
				} else if (v.arg(i).dim.is_vector()) {
					d[y].m().set_row(j,d[x[i]].v());
					j++;
				}
			}
		}

		assert((v.row_vector() && j==v.dim.nb_cols()) || (!v.row_vector() && j==v.dim.nb_rows()));
	}

}

void Eval::gen1_fwd(int x, int y) {
	assert(dynamic_cast<const ExprGenericUnaryOp*>(&(f.node(y))));

	const ExprGenericUnaryOp& e = (const ExprGenericUnaryOp&) f.node(y);
	d[y]=e.eval(d[x]);
}

void Eval::gen2_fwd(int x1, int x2, int y) {
	assert(dynamic_cast<const ExprGenericBinaryOp*>(&(f.node(y))));

	const ExprGenericBinaryOp& e = (const ExprGenericBinaryOp&) f.node(y);
	d[y]=e.eval(d[x1],d[x2]);
}

void Eval::integral_fwd(int* x, int y) {
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
		acb_set_interval(d2[i], d[x[i + 1]].i());
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
	acb_set_interval(a, d[x[0]].i());
	acb_set_interval(b, d[x[1]].i());

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
	if (positive_integrals) {
		i_res |= Interval::pos_reals();
	}
	d[y].i() = i_res;

	acb_clear(res);
	acb_clear(a);
	acb_clear(b);

	for (int i=0; i<n.integrand.nb_arg(); i++) {
		acb_clear(d2[i]);
	}
}

// TODO: One can of course evaluate an integral
// using the IntegralEval class and just convert
// everything back, but there may be some advantage to keeping
// the order=0 queries in the Eval class. This is tricky because
// we still need to eval order=1 queries with IntegralEval.

} // namespace ibex
