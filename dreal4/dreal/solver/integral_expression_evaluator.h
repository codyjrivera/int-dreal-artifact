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
#include <vector>

#include "./ibex.h"

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

using ArbBox = std::unordered_map<Variable, acb_t>;

class IntegralExpressionEvaluator {
 public:
  explicit IntegralExpressionEvaluator();

  // /// Evaluates the expression with @p box.
  // bool operator()(ArbBox& box, acb_ptr res);

  // const Variables& variables() const { return e_.GetVariables(); }

 private:
  bool Visit(const Expression& e, ArbBox& box, acb_t& res);
  static bool VisitVariable(const Expression& e, ArbBox& box, acb_t& res);
  static bool VisitConstant(const Expression& e, ArbBox& box, acb_t& res);
  static bool VisitRealConstant(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitAddition(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitMultiplication(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitDivision(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitLog(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitAbs(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitExp(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitSqrt(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitPow(const Expression& e, ArbBox& box, acb_t& res);

  // Evaluates `pow(e1, e2)` with the @p box.
  bool VisitPow(const Expression& e1, const Expression& e2,
                         ArbBox& box, acb_t& res);
  bool VisitSin(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitCos(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitTan(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitAsin(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitAcos(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitAtan(const Expression& e, ArbBox& box, acb_t& res);
  static bool VisitAtan2(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitSinh(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitCosh(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitTanh(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitMin(const Expression& e, ArbBox& box, acb_t& res);
  bool VisitMax(const Expression& e, ArbBox& box, acb_t& res);
  static bool VisitIfThenElse(const Expression& e, ArbBox& box, acb_t& res);
  static bool VisitUninterpretedFunction(const Expression& e,
                                                  ArbBox& box, acb_t& res);
  bool VisitIntegral(const Expression& e, ArbBox& box, acb_t& res);

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend bool drake::symbolic::VisitExpression<bool>(
      IntegralExpressionEvaluator*, const Expression&, ArbBox&, acb_t&);

  friend std::ostream& operator<<(
      std::ostream& os, const IntegralExpressionEvaluator& expression_evaluator);

  friend int arb_complex_integrand(acb_ptr res, const acb_t z, void* param, slong order, slong prec);

  //const Expression e_;

public: // Integral options
	mag_t integral_tol;
	slong integral_prec, integral_goal;
	acb_calc_integrate_opt_t integral_options;
	double integral_eps = 0.01;
};

struct ComplexIntegrandArgs {
  IntegralExpressionEvaluator* eval;
	const Expression* integral; 
	ArbBox* box;
  bool holomorphic;
};

// Integration scaffolding to pass to arb
int arb_complex_integrand(acb_ptr res, const acb_t z, void* param, slong order, slong prec);

std::ostream& operator<<(std::ostream& os,
                         const IntegralExpressionEvaluator& expression_evaluator);

}  // namespace dreal
