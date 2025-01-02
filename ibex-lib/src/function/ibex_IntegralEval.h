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

#ifndef __IBEX_INTEGRAL_EVAL_H__
#define __IBEX_INTEGRAL_EVAL_H__

#include <iostream>
#include <vector>

#include "ibex_ArbInterface.h"
#include "ibex_ExprDomain.h"
#include "acb.h"
#include "acb_calc.h"

namespace ibex {

using std::vector;

class Function;

/**
 * \ingroup symbolic
 *
 * \brief Function evaluator for integrals, giving
 * a complex Arb ball.
 *
 */
class IntegralEval : public FwdAlgorithm {

public:
	/**
	 * \brief Build the evaluator for the function f.
	 */
	IntegralEval(Function &f);

	/**
	 * \brief Delete this.
	 */
	~IntegralEval();

	/**
	 * \brief Run the forward algorithm with input balls.
	 * Stores the output ball in the location res.
	 * If the integrand is found to be non-holomorphic,
	 * returns false. Otherwise, returns true.
	 */
	bool eval(const vector<acb_t>& d, acb_ptr res);

public: // because called from CompiledFunction

	       void vector_fwd (int* x, int y);
	       void apply_fwd  (int* x, int y);
	inline void idx_fwd    (int x, int y);
	inline void idx_cp_fwd (int x, int y);
	inline void symbol_fwd (int y);
	inline void cst_fwd    (int y);
	inline void chi_fwd    (int x1, int x2, int x3, int y);
	inline void gen2_fwd   (int x, int x2, int y);
	inline void add_fwd    (int x1, int x2, int y);
	inline void mul_fwd    (int x1, int x2, int y);
	inline void sub_fwd    (int x1, int x2, int y);
	inline void div_fwd    (int x1, int x2, int y);
	inline void max_fwd    (int x1, int x2, int y);
	inline void min_fwd    (int x1, int x2, int y);
	inline void atan2_fwd  (int x1, int x2, int y);
	inline void gen1_fwd   (int x, int y);
	inline void minus_fwd  (int x, int y);
	inline void minus_V_fwd(int x, int y);
	inline void minus_M_fwd(int x, int y);
	inline void trans_V_fwd(int x, int y);
	inline void trans_M_fwd(int x, int y);
	inline void sign_fwd   (int x, int y);
	inline void abs_fwd    (int x, int y);
	inline void power_fwd  (int x, int y, int p);
	inline void sqr_fwd    (int x, int y);
	inline void sqrt_fwd   (int x, int y);
	inline void exp_fwd    (int x, int y);
	inline void log_fwd    (int x, int y);
	inline void cos_fwd    (int x, int y);
	inline void sin_fwd    (int x, int y);
	inline void tan_fwd    (int x, int y);
	inline void cosh_fwd    (int x, int y);
	inline void sinh_fwd    (int x, int y);
	inline void tanh_fwd    (int x, int y);
	inline void acos_fwd   (int x, int y);
	inline void asin_fwd   (int x, int y);
	inline void atan_fwd   (int x, int y);
	inline void acosh_fwd  (int x, int y);
	inline void asinh_fwd  (int x, int y);
	inline void atanh_fwd  (int x, int y);
	inline void floor_fwd  (int x, int y);
	inline void ceil_fwd   (int x, int y);
	inline void saw_fwd    (int x, int y);
	inline void add_V_fwd  (int x1, int x2, int y);
	inline void add_M_fwd  (int x1, int x2, int y);
	inline void mul_SV_fwd (int x1, int x2, int y);
	inline void mul_SM_fwd (int x1, int x2, int y);
	inline void mul_VV_fwd (int x1, int x2, int y);
	inline void mul_MV_fwd (int x1, int x2, int y);
	inline void mul_VM_fwd (int x1, int x2, int y);
	inline void mul_MM_fwd (int x1, int x2, int y);
	inline void sub_V_fwd  (int x1, int x2, int y);
	inline void sub_M_fwd  (int x1, int x2, int y);
		   void integral_fwd  (int* x, int y);	

	Function& f;
	vector<acb_t> d; // The state (in ball format).
	vector<int> arg_locs;
	bool holomorphic;

public: 
    // Integral options
	mag_t integral_tol;
	slong integral_prec, integral_goal;
	acb_calc_integrate_opt_t integral_options;
	double integral_eps = 0.01;
};

/* ============================================================================
 	 	 	 	 	 	 	 integration evaluation help
  ============================================================================*/
struct ComplexIntegrandArgs {
	const ExprIntegral* n; 
	vector<acb_t>* d2;
	bool holomorphic;
};

// Integration scaffolding to pass to arb
int arb_complex_integrand(acb_ptr res, const acb_t z, void* param, slong order, slong prec);

/* ============================================================================
 	 	 	 	 	 	 	 implementation
  ============================================================================*/

inline void IntegralEval::idx_fwd(int, int) { /* nothing to do */ }

inline void IntegralEval::symbol_fwd(int) { /* nothing to do */ }

inline void IntegralEval::cst_fwd(int y) {
	const ExprConstant& c = (const ExprConstant&) f.node(y);
	switch (c.type()) {
	case Dim::SCALAR:       
		acb_set_interval(d[y], c.get_value());
		break;
	case Dim::ROW_VECTOR:
	case Dim::COL_VECTOR:
	case Dim::MATRIX: 
		not_implemented("vector or matrix constants");
		break;
	}
}

/**
 * The current implementation is conservative about maintaining holomorphicity, except for the absolute
 * value and square root.
 * TODO: make this less conservative.
 */
inline void IntegralEval::chi_fwd(int x1, int x2, int x3, int y) { not_implemented("chi function"); }
inline void IntegralEval::add_fwd(int x1, int x2, int y)   { acb_add(d[y], d[x1], d[x2], integral_prec); }
inline void IntegralEval::mul_fwd(int x1, int x2, int y)   { acb_mul(d[y], d[x1], d[x2], integral_prec); }
inline void IntegralEval::sub_fwd(int x1, int x2, int y)   { acb_sub(d[y], d[x1], d[x2], integral_prec); }
inline void IntegralEval::div_fwd(int x1, int x2, int y)   { acb_div(d[y], d[x1], d[x2], integral_prec);
                                                             if (arb_contains_zero(acb_realref(d[x2])))
															 	ibex_error("division by zero"); }
inline void IntegralEval::max_fwd(int x1, int x2, int y)   { acb_real_max(d[y], d[x1], d[x2], 0, integral_prec);
															 this->holomorphic = false; }
inline void IntegralEval::min_fwd(int x1, int x2, int y)   { acb_real_min(d[y], d[x1], d[x2], 0, integral_prec);
															 this->holomorphic = false; }
inline void IntegralEval::atan2_fwd(int x1, int x2, int y) { not_implemented("atan2 function"); }

inline void IntegralEval::minus_fwd(int x, int y)          { acb_neg(d[y], d[x]); }
inline void IntegralEval::minus_V_fwd(int x, int y)        { not_implemented("vector/matrix operations"); }
inline void IntegralEval::minus_M_fwd(int x, int y)        { not_implemented("vector/matrix operations"); }
inline void IntegralEval::sign_fwd(int x, int y)           { acb_real_sgn(d[y], d[x], 0, integral_prec);
                                                             if (arb_contains_zero(acb_realref(d[x])))
															 	this->holomorphic = false; }
inline void IntegralEval::abs_fwd(int x, int y)            { acb_real_abs(d[y], d[x], 0, integral_prec);
                                                             if (arb_contains_zero(acb_realref(d[x])))
															 	this->holomorphic = false; }
inline void IntegralEval::power_fwd(int x, int y, int p)   { acb_pow_si(d[y], d[x], p, integral_prec);
															 if (p < 0) {
																not_implemented("negative constant powers not handled properly");
															 } }
inline void IntegralEval::sqr_fwd(int x, int y)            { acb_sqr(d[y], d[x], integral_prec); }
inline void IntegralEval::sqrt_fwd(int x, int y)           { acb_sqrt(d[y], d[x], integral_prec);
                                                             if (arb_contains_zero(acb_imagref(d[x])) &&
																arb_contains_nonpositive(acb_realref(d[x])))
															 	this->holomorphic = false; // conservative approximation
														   }
inline void IntegralEval::exp_fwd(int x, int y)            { acb_exp(d[y], d[x], integral_prec); }
inline void IntegralEval::log_fwd(int x, int y)            { acb_log(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; } // Are we being too conservative?
inline void IntegralEval::cos_fwd(int x, int y)            { acb_cos(d[y], d[x], integral_prec); }
inline void IntegralEval::sin_fwd(int x, int y)            { acb_sin(d[y], d[x], integral_prec); }
inline void IntegralEval::tan_fwd(int x, int y)            { acb_tan(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::cosh_fwd(int x, int y)           { acb_cosh(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::sinh_fwd(int x, int y)           { acb_sinh(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::tanh_fwd(int x, int y)           { acb_tanh(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::acos_fwd(int x, int y)           { acb_acos(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::asin_fwd(int x, int y)           { acb_asin(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::atan_fwd(int x, int y)           { acb_atan(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::acosh_fwd(int x, int y)          { acb_acosh(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::asinh_fwd(int x, int y)          { acb_asinh(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::atanh_fwd(int x, int y)          { acb_atanh(d[y], d[x], integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::floor_fwd(int x, int y)          { acb_real_floor(d[y], d[x], 0, integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::ceil_fwd(int x, int y)           { acb_real_ceil(d[y], d[x], 0, integral_prec);
                                                             this->holomorphic = false; }
inline void IntegralEval::saw_fwd(int x, int y)            { not_implemented("sawtooth function"); }

inline void IntegralEval::trans_V_fwd(int x, int y)        { not_implemented("vector/matrix operations"); }
inline void IntegralEval::trans_M_fwd(int x, int y)        { not_implemented("vector/matrix operations"); }
inline void IntegralEval::add_V_fwd(int x1, int x2, int y) { not_implemented("vector/matrix operations"); }
inline void IntegralEval::add_M_fwd(int x1, int x2, int y) { not_implemented("vector/matrix operations"); }
inline void IntegralEval::mul_SV_fwd(int x1, int x2, int y){ not_implemented("vector/matrix operations"); }
inline void IntegralEval::mul_SM_fwd(int x1, int x2, int y){ not_implemented("vector/matrix operations"); }
inline void IntegralEval::mul_VV_fwd(int x1, int x2, int y){ not_implemented("vector/matrix operations"); }
inline void IntegralEval::mul_MV_fwd(int x1, int x2, int y){ not_implemented("vector/matrix operations"); }
inline void IntegralEval::mul_VM_fwd(int x1, int x2, int y){ not_implemented("vector/matrix operations"); }
inline void IntegralEval::mul_MM_fwd(int x1, int x2, int y){ not_implemented("vector/matrix operations"); }
inline void IntegralEval::sub_V_fwd(int x1, int x2, int y) { not_implemented("vector/matrix operations"); }
inline void IntegralEval::sub_M_fwd(int x1, int x2, int y) { not_implemented("vector/matrix operations"); }

} // namespace ibex

#endif // __IBEX_EVAL_H__
