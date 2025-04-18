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
#pragma once

#include <ostream>

#include "./ibex.h"

#include "dreal/solver/integral_expression_evaluator.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

class ExpressionEvaluator {
 public:
  explicit ExpressionEvaluator(Expression e);

  /// Evaluates the expression with @p box.
  Box::Interval operator()(const Box& box) const;

  const Variables& variables() const { return e_.GetVariables(); }

 private:
  Box::Interval Visit(const Expression& e, const Box& box) const;
  static Box::Interval VisitVariable(const Expression& e, const Box& box);
  static Box::Interval VisitConstant(const Expression& e, const Box& box);
  static Box::Interval VisitRealConstant(const Expression& e, const Box& box);
  Box::Interval VisitAddition(const Expression& e, const Box& box) const;
  Box::Interval VisitMultiplication(const Expression& e, const Box& box) const;
  Box::Interval VisitDivision(const Expression& e, const Box& box) const;
  Box::Interval VisitLog(const Expression& e, const Box& box) const;
  Box::Interval VisitAbs(const Expression& e, const Box& box) const;
  Box::Interval VisitExp(const Expression& e, const Box& box) const;
  Box::Interval VisitSqrt(const Expression& e, const Box& box) const;
  Box::Interval VisitPow(const Expression& e, const Box& box) const;

  // Evaluates `pow(e1, e2)` with the @p box.
  Box::Interval VisitPow(const Expression& e1, const Expression& e2,
                         const Box& box) const;
  Box::Interval VisitSin(const Expression& e, const Box& box) const;
  Box::Interval VisitCos(const Expression& e, const Box& box) const;
  Box::Interval VisitTan(const Expression& e, const Box& box) const;
  Box::Interval VisitAsin(const Expression& e, const Box& box) const;
  Box::Interval VisitAcos(const Expression& e, const Box& box) const;
  Box::Interval VisitAtan(const Expression& e, const Box& box) const;
  Box::Interval VisitAtan2(const Expression& e, const Box& box) const;
  Box::Interval VisitSinh(const Expression& e, const Box& box) const;
  Box::Interval VisitCosh(const Expression& e, const Box& box) const;
  Box::Interval VisitTanh(const Expression& e, const Box& box) const;
  Box::Interval VisitMin(const Expression& e, const Box& box) const;
  Box::Interval VisitMax(const Expression& e, const Box& box) const;
  static Box::Interval VisitIfThenElse(const Expression& e, const Box& box);
  static Box::Interval VisitUninterpretedFunction(const Expression& e,
                                                  const Box& box);
  Box::Interval VisitIntegral(const Expression& e, const Box& box) const;

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Box::Interval drake::symbolic::VisitExpression<Box::Interval>(
      const ExpressionEvaluator*, const Expression&, const Box&);

  friend std::ostream& operator<<(
      std::ostream& os, const ExpressionEvaluator& expression_evaluator);

  friend int arb_integrand(acb_ptr res, const acb_t z, void* param, slong order, slong prec);

  const Expression e_;

public: // Integral options
	mag_t integral_tol;
	slong integral_prec, integral_goal;
	acb_calc_integrate_opt_t integral_options;
	double integral_eps = 0.01;
};

std::ostream& operator<<(std::ostream& os,
                         const ExpressionEvaluator& expression_evaluator);

}  // namespace dreal
