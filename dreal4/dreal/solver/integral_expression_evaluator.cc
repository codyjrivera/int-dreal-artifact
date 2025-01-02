/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#include "dreal/solver/integral_expression_evaluator.h"

#include <algorithm>  // to suppress cpplint for the use of 'min'
#include <numeric>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"
#include "dreal/util/math.h"

namespace dreal {

using std::accumulate;
using std::pair;

#define PREC 128

IntegralExpressionEvaluator::IntegralExpressionEvaluator() {
  // Default integral initialization
	integral_prec = PREC;
	integral_goal = integral_prec;
	mag_init(integral_tol);
	mag_set_ui_2exp_si(integral_tol, 1, -integral_prec);
	acb_calc_integrate_opt_init(integral_options);
	integral_eps = 0.01;
}

/*bool IntegralExpressionEvaluator::operator()(ArbBox& box, acb_ptr res) {
  return Visit(e_, box, res);
}*/

bool IntegralExpressionEvaluator::Visit(
  const Expression& e, ArbBox& box, acb_t& res
) {
  return VisitExpression<bool>(this, e, box, res);
}

bool IntegralExpressionEvaluator::VisitVariable(
  const Expression& e, ArbBox& box, acb_t& res
) {
  const Variable& var{get_variable(e)};
  acb_set(res, box[var]);
  return true;
}

bool IntegralExpressionEvaluator::VisitConstant(
  const Expression& e, ArbBox& /* unused */, acb_t& res
) {
  const double c{get_constant_value(e)};
  acb_set_d(res, c);
  return true;
}

bool IntegralExpressionEvaluator::VisitRealConstant(
  const Expression& e, ArbBox& /* unused */, acb_t& res
) {
  const double lb{get_lb_of_real_constant(e)};
  const double ub{get_ub_of_real_constant(e)};
  Box::Interval i{lb, ub};
  ibex::acb_set_interval(res, i);
  return true;
}

bool IntegralExpressionEvaluator::VisitAddition(
  const Expression& e, ArbBox& box, acb_t& res
) {
  const double c{get_constant_in_addition(e)};
  const auto& expr_to_coeff_map = get_expr_to_coeff_map_in_addition(e);

  acb_t inner_res, cst;
  bool holo = true;

  acb_init(inner_res);
  acb_init(cst);

  acb_set_d(res, c);

  auto first = expr_to_coeff_map.begin();
  auto last = expr_to_coeff_map.end();

  for (; first != last; ++first) {
    auto p = *first;
    holo = holo && Visit(p.first, box, inner_res);
    acb_set_d(cst, p.second);
    acb_mul(inner_res, inner_res, cst, integral_prec);
    acb_add(res, res, inner_res, integral_prec);
  }

  acb_clear(inner_res);
  acb_clear(cst);

  return holo;
}

bool IntegralExpressionEvaluator::VisitMultiplication(
  const Expression& e, ArbBox& box, acb_t& res
) {
  const double c{get_constant_in_multiplication(e)};
  const auto& base_to_exponent_map =
      get_base_to_exponent_map_in_multiplication(e);

  acb_t inner_res;
  bool holo = true;

  acb_init(inner_res);
  acb_set_d(res, c);

  auto first = base_to_exponent_map.begin();
  auto last = base_to_exponent_map.end();

  for (; first != last; ++first) {
    auto p = *first;
    holo = holo && VisitPow(p.first, p.second, box, inner_res);
    acb_mul(res, res, inner_res, integral_prec);
  }

  acb_clear(inner_res);

  return holo;
}

bool IntegralExpressionEvaluator::VisitDivision(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a, b;
  bool holo = true;

  acb_init(a);
  acb_init(b);

  holo = holo && Visit(get_first_argument(e), box, a);
  holo = holo && Visit(get_second_argument(e), box, b);

  acb_div(res, a, b, integral_prec);

  if (arb_contains_zero(acb_realref(b)))
    throw DREAL_RUNTIME_ERROR("Division by zero in integral.");

  acb_clear(a);
  acb_clear(b);

  return holo;
}

bool IntegralExpressionEvaluator::VisitLog(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;
  bool holo = true;

  acb_init(a);
  holo = holo && Visit(get_argument(e), box, a);
  acb_log(res, a, integral_prec);

  // if (arb_contains_nonpositive(acb_realref(a)))
  //   holo = false;

  acb_clear(a);

  return false; // For now, be consistent.
}

bool IntegralExpressionEvaluator::VisitAbs(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;
  bool holo = true;

  acb_init(a);
  holo = holo && Visit(get_argument(e), box, a);
  acb_real_abs(res, a, 0, integral_prec);

  if (arb_contains_zero(acb_realref(a)))
    holo = false;

  acb_clear(a);

  return holo;
}

bool IntegralExpressionEvaluator::VisitExp(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;
  bool holo = true;

  acb_init(a);
  holo = holo && Visit(get_argument(e), box, a);
  acb_exp(res, a, integral_prec);

  acb_clear(a);

  return holo;
}

bool IntegralExpressionEvaluator::VisitSqrt(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;
  bool holo = true;

  acb_init(a);
  holo = holo && Visit(get_argument(e), box, a);
  acb_sqrt(res, a, integral_prec);

  if (arb_contains_zero(acb_imagref(a))
     && arb_contains_nonpositive(acb_realref(a)))
		holo = false; // conservative approximation

  acb_clear(a);

  return holo;
}

bool IntegralExpressionEvaluator::VisitPow(
  const Expression& e, ArbBox& box, acb_t& res
) {
  return VisitPow(get_first_argument(e), get_second_argument(e), box, res);
}

bool IntegralExpressionEvaluator::VisitPow(
  const Expression& e1,
  const Expression& e2,
  ArbBox& box,
  acb_t& res
) {
  acb_t a, b;
  bool holo = true;

  acb_init(a);
  acb_init(b);

  holo = holo && Visit(e1, box, a);
  holo = holo && Visit(e2, box, b);

  acb_pow(res, a, b, integral_prec);

  if (!arb_is_exact(acb_realref(b))
    || !arb_is_zero(acb_imagref(b)))
    holo = false;

  acb_clear(a);
  acb_clear(b);

  return holo;
}

bool IntegralExpressionEvaluator::VisitSin(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;
  bool holo = true;

  acb_init(a);
  holo = holo && Visit(get_argument(e), box, a);
  acb_sin(res, a, integral_prec);

  acb_clear(a);

  return holo;
}

bool IntegralExpressionEvaluator::VisitCos(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;
  bool holo = true;

  acb_init(a);
  holo = holo && Visit(get_argument(e), box, a);
  acb_cos(res, a, integral_prec);

  acb_clear(a);

  return holo;
}

bool IntegralExpressionEvaluator::VisitTan(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_tan(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitAsin(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_asin(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitAcos(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_acos(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitAtan(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_atan(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitAtan2(
  const Expression& /*unused*/, ArbBox& /*unused*/, acb_t& /*unused*/
) {
  throw DREAL_RUNTIME_ERROR("atan2 expression is not supported yet in integrals.");
}

bool IntegralExpressionEvaluator::VisitSinh(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_sinh(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitCosh(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_cosh(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitTanh(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a;

  acb_init(a);
  Visit(get_argument(e), box, a);
  acb_tanh(res, a, integral_prec);

  acb_clear(a);

  return false;
}

bool IntegralExpressionEvaluator::VisitMin(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a, b;

  acb_init(a);
  acb_init(b);

  Visit(get_first_argument(e), box, a);
  Visit(get_second_argument(e), box, b);

  acb_real_min(res, a, b, 0, integral_prec);

  acb_clear(a);
  acb_clear(b);

  return false;
}

bool IntegralExpressionEvaluator::VisitMax(
  const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a, b;

  acb_init(a);
  acb_init(b);

  Visit(get_first_argument(e), box, a);
  Visit(get_second_argument(e), box, b);

  acb_real_max(res, a, b, 0, integral_prec);

  acb_clear(a);
  acb_clear(b);

  return false;
}

bool IntegralExpressionEvaluator::VisitIfThenElse(
  const Expression& /*unused*/, ArbBox& /*unused*/, acb_t& /*unused*/
) {
  throw DREAL_RUNTIME_ERROR("If-then-else expression is not supported yet.");
}

bool IntegralExpressionEvaluator::VisitUninterpretedFunction(
  const Expression& /*unused*/, ArbBox& /*unused*/, acb_t& /*unused*/
) {
  throw DREAL_RUNTIME_ERROR("Uninterpreted function is not supported.");
}

// Much room for optimization, I think.
bool IntegralExpressionEvaluator::VisitIntegral(
    const Expression& e, ArbBox& box, acb_t& res
) {
  acb_t a, b, oldiv;
  bool holo = true;

  acb_init(a);
  acb_init(b);
  acb_init(oldiv);
  
  holo = holo && Visit(get_left_endpoint(e), box, a);
  holo = holo && Visit(get_right_endpoint(e), box, b);

  ArbBox inner(box);

  bool already_defined = inner.find(get_integration_var(e)) != inner.end();

  if (already_defined) {
    acb_set(oldiv, inner[get_integration_var(e)]);
  } else {
    acb_init(inner[get_integration_var(e)]);
  }

  ComplexIntegrandArgs args;
  args.eval = this;
  args.integral = &e;
  args.box = &inner;
  args.holomorphic = true;
  
  acb_zero(res);
  acb_calc_integrate(
		res, 
		&arb_complex_integrand, 
		static_cast<void*>(&args), 
		a, b, 
		integral_goal, 
		integral_tol,
		integral_options,
		integral_prec
	);

  holo = holo && args.holomorphic;

  if (already_defined) {
    acb_set(inner[get_integration_var(e)], oldiv);
  } else {
    acb_clear(inner[get_integration_var(e)]);
  }

  acb_clear(a);
  acb_clear(b);
  acb_clear(oldiv);
  
  return holo;
}

std::ostream& operator<<(std::ostream& os,
                         const IntegralExpressionEvaluator& /* unused */) {
  return os << "IntegralExpressionEvaluator()";
}

// Integration scaffolding to pass to arb
int arb_complex_integrand(acb_ptr res, const acb_t z, void* param, slong order, slong /* It's no use */) {
	assert(param != NULL);
	ComplexIntegrandArgs* args = static_cast<ComplexIntegrandArgs*>(param);
  IntegralExpressionEvaluator& eval = *(args->eval);
	const Expression& integral = *(args->integral);
	ArbBox& box = *(args->box);

	if (order > 1)
		flint_abort();

  acb_t tmp_res;
  acb_init(tmp_res);

	acb_set(box[get_integration_var(integral)], z);

	bool holo = eval.Visit(get_integrand(integral), box, tmp_res);

  acb_set(res, tmp_res);

  if (order == 1 && !holo) {
		acb_indeterminate(res);
	}

  if (!holo) {
    args->holomorphic = false;
  }

  acb_clear(tmp_res);

	return 0;
}

}  // namespace dreal
