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
#include "dreal/solver/expression_evaluator.h"

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

ExpressionEvaluator::ExpressionEvaluator(Expression e) : e_{std::move(e)} {
  // Default integral initialization
	integral_prec = PREC;
	integral_goal = integral_prec;
	mag_init(integral_tol);
	mag_set_ui_2exp_si(integral_tol, 1, -integral_prec);
	acb_calc_integrate_opt_init(integral_options);
	integral_eps = 0.01;
}

Box::Interval ExpressionEvaluator::operator()(const Box& box) const {
  return Visit(e_, box);
}

Box::Interval ExpressionEvaluator::Visit(const Expression& e,
                                         const Box& box) const {
  return VisitExpression<Box::Interval>(this, e, box);
}

Box::Interval ExpressionEvaluator::VisitVariable(const Expression& e,
                                                 const Box& box) {
  const Variable& var{get_variable(e)};
  return box[var];
}

Box::Interval ExpressionEvaluator::VisitConstant(const Expression& e,
                                                 const Box& /* unused */) {
  const double c{get_constant_value(e)};
  return Box::Interval{c};
}

Box::Interval ExpressionEvaluator::VisitRealConstant(const Expression& e,
                                                     const Box& /* unused */) {
  const double lb{get_lb_of_real_constant(e)};
  const double ub{get_ub_of_real_constant(e)};
  return Box::Interval{lb, ub};
}

Box::Interval ExpressionEvaluator::VisitAddition(const Expression& e,
                                                 const Box& box) const {
  const double c{get_constant_in_addition(e)};
  const auto& expr_to_coeff_map = get_expr_to_coeff_map_in_addition(e);
  return accumulate(expr_to_coeff_map.begin(), expr_to_coeff_map.end(),
                    ibex::Interval{c},
                    [this, &box](const Box::Interval& init,
                                 const pair<const Expression, double>& p) {
                      return init + Visit(p.first, box) * p.second;
                    });
}

Box::Interval ExpressionEvaluator::VisitMultiplication(const Expression& e,
                                                       const Box& box) const {
  const double c{get_constant_in_multiplication(e)};
  const auto& base_to_exponent_map =
      get_base_to_exponent_map_in_multiplication(e);
  return accumulate(base_to_exponent_map.begin(), base_to_exponent_map.end(),
                    ibex::Interval{c},
                    [this, &box](const Box::Interval& init,
                                 const pair<const Expression, Expression>& p) {
                      return init * VisitPow(p.first, p.second, box);
                    });
}

Box::Interval ExpressionEvaluator::VisitDivision(const Expression& e,
                                                 const Box& box) const {
  return Visit(get_first_argument(e), box) / Visit(get_second_argument(e), box);
}

Box::Interval ExpressionEvaluator::VisitLog(const Expression& e,
                                            const Box& box) const {
  return log(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitAbs(const Expression& e,
                                            const Box& box) const {
  return abs(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitExp(const Expression& e,
                                            const Box& box) const {
  return exp(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitSqrt(const Expression& e,
                                             const Box& box) const {
  return sqrt(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitPow(const Expression& e,
                                            const Box& box) const {
  return VisitPow(get_first_argument(e), get_second_argument(e), box);
}

Box::Interval ExpressionEvaluator::VisitPow(const Expression& e1,
                                            const Expression& e2,
                                            const Box& box) const {
  const Box::Interval first{Visit(e1, box)};
  const Box::Interval second{Visit(e2, box)};
  if (second.is_degenerated() && !second.is_empty()) {
    // This indicates that this interval is a point.
    DREAL_ASSERT(second.lb() == second.ub());
    const double point{second.lb()};
    if (is_integer(point)) {
      if (point == 2.0) {
        return sqr(first);
      } else {
        return pow(first, static_cast<int>(point));
      }
    } else {
      return pow(first, point);
    }
  } else {
    return pow(first, second);
  }
}

Box::Interval ExpressionEvaluator::VisitSin(const Expression& e,
                                            const Box& box) const {
  return sin(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitCos(const Expression& e,
                                            const Box& box) const {
  return cos(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitTan(const Expression& e,
                                            const Box& box) const {
  return tan(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitAsin(const Expression& e,
                                             const Box& box) const {
  return asin(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitAcos(const Expression& e,
                                             const Box& box) const {
  return acos(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitAtan(const Expression& e,
                                             const Box& box) const {
  return atan(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitAtan2(const Expression& e,
                                              const Box& box) const {
  return atan2(Visit(get_first_argument(e), box),
               Visit(get_second_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitSinh(const Expression& e,
                                             const Box& box) const {
  return sinh(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitCosh(const Expression& e,
                                             const Box& box) const {
  return cosh(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitTanh(const Expression& e,
                                             const Box& box) const {
  return tanh(Visit(get_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitMin(const Expression& e,
                                            const Box& box) const {
  return min(Visit(get_first_argument(e), box),
             Visit(get_second_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitMax(const Expression& e,
                                            const Box& box) const {
  return max(Visit(get_first_argument(e), box),
             Visit(get_second_argument(e), box));
}

Box::Interval ExpressionEvaluator::VisitIfThenElse(
    const Expression& /* unused */, const Box& /* unused */) {
  throw DREAL_RUNTIME_ERROR("If-then-else expression is not supported yet.");
}

Box::Interval ExpressionEvaluator::VisitUninterpretedFunction(
    const Expression& /* unused */, const Box& /* unused */) {
  throw DREAL_RUNTIME_ERROR("Uninterpreted function is not supported.");
}

// Much room for optimization, I think.
Box::Interval ExpressionEvaluator::VisitIntegral(
    const Expression& e, const Box& box) const {

  Box::Interval ibex_a = Visit(get_left_endpoint(e), box);
  Box::Interval ibex_b = Visit(get_right_endpoint(e), box);

  ArbBox inner;
  Variable iv = get_integration_var(e);

  for (int i = 0; i < box.size(); ++i) {
    Variable v = box.variable(i);
    if (v != iv) {
      acb_init(inner[v]);
      ibex::acb_set_interval(inner[v], box[i]);
    }
  }
  acb_init(inner[iv]);

  IntegralExpressionEvaluator eval;
  ComplexIntegrandArgs args;
  args.eval = &eval;
  args.integral = &e;
  args.box = &inner;
  args.holomorphic = true;
  
  acb_t a, b, res;
  acb_init(a);
  acb_init(b);
  acb_init(res);
  acb_zero(res);

  ibex::acb_set_interval(a, ibex_a);
  ibex::acb_set_interval(b, ibex_b);

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

  Box::Interval ibex_res = ibex::acb_get_interval(res);

  for (int i = 0; i < box.size(); ++i) {
    Variable v = box.variable(i);
    if (v != iv) {
      acb_clear(inner[v]);
    }
  }
  acb_clear(inner[iv]);

  acb_clear(a);
  acb_clear(b);
  acb_clear(res);
  
  return ibex_res;
}

std::ostream& operator<<(std::ostream& os,
                         const ExpressionEvaluator& expression_evaluator) {
  return os << "ExpressionEvaluator(" << expression_evaluator.e_ << ")";
}

}  // namespace dreal
