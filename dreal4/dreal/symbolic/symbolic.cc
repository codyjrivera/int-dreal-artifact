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
#include "dreal/symbolic/symbolic.h"

#include <algorithm>
#include <iterator>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::all_of;
using std::function;
using std::inserter;
using std::ostream;
using std::pair;
using std::set;
using std::string;
using std::to_string;
using std::transform;
using std::vector;

Formula imply(const Formula& f1, const Formula& f2) { return !f1 || f2; }
Formula imply(const Variable& v, const Formula& f) {
  return imply(Formula{v}, f);
}
Formula imply(const Formula& f, const Variable& v) {
  return imply(f, Formula{v});
}
Formula imply(const Variable& v1, const Variable& v2) {
  return imply(Formula{v1}, Formula{v2});
}

Formula iff(const Formula& f1, const Formula& f2) {
  return imply(f1, f2) && imply(f2, f1);
}

Formula iff(const Variable& v, const Formula& f) { return iff(Formula{v}, f); }

Formula iff(const Formula& f, const Variable& v) { return iff(f, Formula{v}); }

Formula iff(const Variable& v1, const Variable& v2) {
  return iff(Formula{v1}, Formula{v2});
}

set<Formula> map(const set<Formula>& formulas,
                 const function<Formula(const Formula&)>& func) {
  set<Formula> result;
  transform(formulas.cbegin(), formulas.cend(),
            inserter(result, result.begin()), func);
  return result;
}

bool is_atomic(const Formula& f) {
  switch (f.get_kind()) {
    case FormulaKind::False:
    case FormulaKind::True:
    case FormulaKind::Var:
    case FormulaKind::Eq:
    case FormulaKind::Neq:
    case FormulaKind::Gt:
    case FormulaKind::Geq:
    case FormulaKind::Lt:
    case FormulaKind::Leq:
    case FormulaKind::Forall:
      return true;
    case FormulaKind::And:
    case FormulaKind::Or:
      return false;
    case FormulaKind::Not: {
      const Formula& negated_formula{get_operand(f)};
      return is_variable(negated_formula) || is_relational(negated_formula);
    }
  }
  DREAL_UNREACHABLE();
}

bool is_clause(const Formula& f) {
  if (is_atomic(f)) {
    return true;
  }
  if (is_negation(f)) {
    return is_atomic(get_operand(f));
  }
  if (is_conjunction(f)) {
    return false;
  }
  if (is_disjunction(f)) {
    const auto& operands = get_operands(f);
    const bool result{
        all_of(operands.cbegin(), operands.cend(),
               [](const Formula& formula) { return is_atomic(formula); })};
    return result;
  }
  DREAL_UNREACHABLE();
}

set<Formula> get_clauses(const Formula& f) {
  if (is_conjunction(f)) {
#ifndef NDEBUG
    for (const Formula& clause : get_operands(f)) {
      DREAL_ASSERT(is_clause(clause));
    }
#endif
    return get_operands(f);
  } else {
    DREAL_ASSERT(is_clause(f));
    return {f};
  }
}

bool is_cnf(const Formula& f) {
  if (is_atomic(f)) {
    return true;
  }
  if (is_disjunction(f)) {
    return is_clause(f);
  }
  if (is_conjunction(f)) {
    const auto& operands = get_operands(f);
    const bool result{
        all_of(operands.cbegin(), operands.cend(),
               [](const Formula& formula) { return is_clause(formula); })};
    return result;
  }
  DREAL_UNREACHABLE();
}

bool HaveIntersection(const Variables& variables1,
                      const Variables& variables2) {
  auto begin1 = variables1.begin();
  auto begin2 = variables2.begin();
  const auto end1 = variables1.end();
  const auto end2 = variables2.end();
  while (begin1 != end1 && begin2 != end2) {
    if (begin1->less(*begin2)) {
      ++begin1;
    } else {
      if (!begin2->less(*begin1)) {
        return true;
      }
      ++begin2;
    }
  }
  return false;
}

namespace {
/// Visitor class which strengthens a formula by delta.
class DeltaStrengthenVisitor {
 public:
  DeltaStrengthenVisitor() = default;
  Formula Strengthen(const Formula& f, const double delta) const {
    if (delta == 0) {
      return f;
    }
    return Visit(f, delta);
  }

 private:
  Expression Visit(const Expression& e, const double delta) const {
    return VisitExpression<Expression>(this, e, delta);
  }
  Expression VisitVariable(const Expression& e, const double) const {
    return e;
  }
  Expression VisitConstant(const Expression& e, const double) const {
    return e;
  }
  Expression VisitRealConstant(const Expression& e, const double) const {
    return e;
  }
  Expression VisitAddition(const Expression& e, const double delta) const {
    Expression ret{get_constant_in_addition(e)};
    for (const auto& p : get_expr_to_coeff_map_in_addition(e)) {
      const Expression& e_i{p.first};
      const double coeff{p.second};
      ret += coeff * Visit(e_i, delta);
    }
    return ret;
  }
  Expression VisitMultiplication(const Expression& e,
                                 const double delta) const {
    Expression ret{get_constant_in_multiplication(e)};
    for (const auto& p : get_base_to_exponent_map_in_multiplication(e)) {
      const Expression& base{p.first};
      const Expression& exponent{p.second};
      ret *= pow(Visit(base, delta), Visit(exponent, delta));
    }
    return ret;
  }
  Expression VisitDivision(const Expression& e, const double delta) const {
    return Visit(get_first_argument(e), delta) /
           Visit(get_second_argument(e), delta);
  }
  Expression VisitLog(const Expression& e, const double delta) const {
    return log(Visit(get_argument(e), delta));
  }
  Expression VisitAbs(const Expression& e, const double delta) const {
    return abs(Visit(get_argument(e), delta));
  }
  Expression VisitExp(const Expression& e, const double delta) const {
    return exp(Visit(get_argument(e), delta));
  }
  Expression VisitSqrt(const Expression& e, const double delta) const {
    return sqrt(Visit(get_argument(e), delta));
  }
  Expression VisitPow(const Expression& e, const double delta) const {
    return pow(Visit(get_first_argument(e), delta),
               Visit(get_second_argument(e), delta));
  }
  Expression VisitSin(const Expression& e, const double delta) const {
    return sin(Visit(get_argument(e), delta));
  }
  Expression VisitCos(const Expression& e, const double delta) const {
    return cos(Visit(get_argument(e), delta));
  }
  Expression VisitTan(const Expression& e, const double delta) const {
    return tan(Visit(get_argument(e), delta));
  }
  Expression VisitAsin(const Expression& e, const double delta) const {
    return asin(Visit(get_argument(e), delta));
  }
  Expression VisitAcos(const Expression& e, const double delta) const {
    return acos(Visit(get_argument(e), delta));
  }
  Expression VisitAtan(const Expression& e, const double delta) const {
    return atan(Visit(get_argument(e), delta));
  }
  Expression VisitAtan2(const Expression& e, const double delta) const {
    return atan2(Visit(get_first_argument(e), delta),
                 Visit(get_second_argument(e), delta));
  }
  Expression VisitSinh(const Expression& e, const double delta) const {
    return sinh(Visit(get_argument(e), delta));
  }
  Expression VisitCosh(const Expression& e, const double delta) const {
    return cosh(Visit(get_argument(e), delta));
  }
  Expression VisitTanh(const Expression& e, const double delta) const {
    return tanh(Visit(get_argument(e), delta));
  }
  Expression VisitMin(const Expression& e, const double delta) const {
    return min(Visit(get_first_argument(e), delta),
               Visit(get_second_argument(e), delta));
  }
  Expression VisitMax(const Expression& e, const double delta) const {
    return max(Visit(get_first_argument(e), delta),
               Visit(get_second_argument(e), delta));
  }
  Expression VisitIfThenElse(const Expression& e, const double delta) const {
    return if_then_else(Visit(get_conditional_formula(e), delta),
                        Visit(get_then_expression(e), delta),
                        Visit(get_else_expression(e), delta));
  }
  Expression VisitUninterpretedFunction(const Expression& e,
                                        const double) const {
    return e;
  }
  Expression VisitIntegral(const Expression& e,
                           const double delta) const {
    return integral(get_integration_var(e),
                    Visit(get_left_endpoint(e), delta),
                    Visit(get_right_endpoint(e), delta),
                    Visit(get_integrand(e), delta));
  }

  Formula Visit(const Formula& f, const double delta) const {
    return VisitFormula<Formula>(this, f, delta);
  }
  Formula VisitFalse(const Formula& f, const double) const { return f; }
  Formula VisitTrue(const Formula& f, const double) const { return f; }
  Formula VisitVariable(const Formula& f, const double) const { return f; }
  Formula VisitEqualTo(const Formula& f, const double delta) const {
    if (delta > 0) {
      DREAL_LOG_WARN(
          "Strengthening {} with {} results in false. However, we return {}.",
          f, delta, f);
      return f;
    } else {
      //     lhs = rhs
      // -> (lhs >= rhs) ∧ (lhs <= rhs)
      const Expression lhs{Visit(get_lhs_expression(f), delta)};
      const Expression rhs{Visit(get_rhs_expression(f), delta)};
      return VisitGreaterThanOrEqualTo(lhs >= rhs, delta) &&
             VisitLessThanOrEqualTo(lhs <= rhs, delta);
    }
  }
  Formula VisitNotEqualTo(const Formula& f, const double delta) const {
    if (delta > 0) {
      //     lhs ≠ rhs
      // -> (lhs > rhs) ∨ (lhs < rhs)
      const Expression lhs{Visit(get_lhs_expression(f), delta)};
      const Expression rhs{Visit(get_rhs_expression(f), delta)};
      return VisitGreaterThan(lhs > rhs, delta) ||
             VisitLessThan(lhs < rhs, delta);
    } else {
      return Formula::True();
    }
  }
  Formula VisitGreaterThan(const Formula& f, const double delta) const {
    //     lhs > rhs
    //
    // After strengthening, we have:
    //     (lhs > rhs + delta)
    const Expression lhs{Visit(get_lhs_expression(f), delta)};
    const Expression rhs{Visit(get_rhs_expression(f), delta)};
    if (is_variable(rhs)) {
      // We return the following so that possibly we can keep the
      // bounded constraint form (c relop. v) where c is a constant.
      // Keeping this syntactic form is useful because our
      // FilterAssertion relies on that.
      return (lhs - delta > rhs);
    } else {
      return (lhs > rhs + delta);
    }
  }
  Formula VisitGreaterThanOrEqualTo(const Formula& f,
                                    const double delta) const {
    //     lhs >= rhs
    //
    // After strengthening, we have:
    //     (lhs >= rhs + delta)
    const Expression lhs{Visit(get_lhs_expression(f), delta)};
    const Expression rhs{Visit(get_rhs_expression(f), delta)};
    if (is_variable(rhs)) {
      // We return the following so that possibly we can keep the
      // bounded constraint form (c relop. v) where c is a constant.
      // Keeping this syntactic form is useful because our
      // FilterAssertion relies on that.
      return (lhs - delta >= rhs);
    } else {
      return (lhs >= rhs + delta);
    }
  }
  Formula VisitLessThan(const Formula& f, const double delta) const {
    //     lhs < rhs
    //
    // After strengthening, we have:
    //     (lhs + delta < rhs)
    const Expression lhs{Visit(get_lhs_expression(f), delta)};
    const Expression rhs{Visit(get_rhs_expression(f), delta)};
    if (is_variable(lhs)) {
      // We return the following so that possibly we can keep the
      // bounded constraint form (v relop. c) where c is a constant.
      // Keeping this syntactic form is useful because our
      // FilterAssertion relies on that.
      return (lhs < rhs - delta);
    } else {
      return (lhs + delta < rhs);
    }
  }
  Formula VisitLessThanOrEqualTo(const Formula& f, const double delta) const {
    //     lhs <= rhs
    //
    // After strengthening, we have:
    //     (lhs + delta <= rhs)
    const Expression lhs{Visit(get_lhs_expression(f), delta)};
    const Expression rhs{Visit(get_rhs_expression(f), delta)};
    if (is_variable(lhs)) {
      // We return the following so that possibly we can keep the
      // bounded constraint form (v relop. c) where c is a constant.
      // Keeping this syntactic form is useful because our
      // FilterAssertion relies on that.
      return (lhs <= rhs - delta);
    } else {
      return (lhs + delta <= rhs);
    }
  }
  Formula VisitConjunction(const Formula& f, const double delta) const {
    Formula ret{Formula::True()};
    for (const auto& f_i : get_operands(f)) {
      ret = std::move(ret) && this->Visit(f_i, delta);
    }
    return ret;
  }
  Formula VisitDisjunction(const Formula& f, const double delta) const {
    Formula ret{Formula::False()};
    for (const auto& f_i : get_operands(f)) {
      ret = std::move(ret) || this->Visit(f_i, delta);
    }
    return ret;
  }
  Formula VisitNegation(const Formula& f, const double delta) const {
    return !Visit(get_operand(f), -delta);
  }
  Formula VisitForall(const Formula&, const double) const {
    throw DREAL_RUNTIME_ERROR(
        "DeltaStrengthenVisitor: forall formula is not supported.");
  }

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Expression drake::symbolic::VisitExpression<Expression>(
      const DeltaStrengthenVisitor*, const Expression&, const double&);

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(
      const DeltaStrengthenVisitor*, const Formula&, const double&);
};

/// Visitor class which strengthens a formula by delta.
class IsDifferentiableVisitor {
 public:
  IsDifferentiableVisitor() = default;
  bool Visit(const Formula& f) const { return VisitFormula<bool>(this, f); }
  bool Visit(const Expression& e) const {
    return VisitExpression<bool>(this, e);
  }

 private:
  // Handle Formulas.
  bool VisitFalse(const Formula&) const { return true; }
  bool VisitTrue(const Formula&) const { return true; }
  bool VisitVariable(const Formula&) const { return true; }
  bool VisitEqualTo(const Formula& f) const {
    return Visit(get_lhs_expression(f)) && Visit(get_rhs_expression(f));
  }
  bool VisitNotEqualTo(const Formula& f) const {
    return Visit(get_lhs_expression(f)) && Visit(get_rhs_expression(f));
  }
  bool VisitGreaterThan(const Formula& f) const {
    return Visit(get_lhs_expression(f)) && Visit(get_rhs_expression(f));
  }
  bool VisitGreaterThanOrEqualTo(const Formula& f) const {
    return Visit(get_lhs_expression(f)) && Visit(get_rhs_expression(f));
  }
  bool VisitLessThan(const Formula& f) const {
    return Visit(get_lhs_expression(f)) && Visit(get_rhs_expression(f));
  }
  bool VisitLessThanOrEqualTo(const Formula& f) const {
    return Visit(get_lhs_expression(f)) && Visit(get_rhs_expression(f));
  }
  bool VisitConjunction(const Formula& f) const {
    const auto& operands = get_operands(f);
    return all_of(operands.begin(), operands.end(),
                  [this](const Formula& o) { return Visit(o); });
  }
  bool VisitDisjunction(const Formula& f) const {
    const auto& operands = get_operands(f);
    return all_of(operands.begin(), operands.end(),
                  [this](const Formula& o) { return Visit(o); });
  }
  bool VisitNegation(const Formula& f) const { return Visit(get_operand(f)); }
  bool VisitForall(const Formula&) const { return false; }

  // Handle Expressions.
  bool VisitVariable(const Expression&) const { return true; }
  bool VisitConstant(const Expression&) const { return true; }
  bool VisitRealConstant(const Expression&) const { return true; }
  bool VisitAddition(const Expression& e) const {
    const auto& expr_to_coeff_map = get_expr_to_coeff_map_in_addition(e);
    return all_of(expr_to_coeff_map.begin(), expr_to_coeff_map.end(),
                  [this](const pair<const Expression, double>& p) {
                    const Expression& e_i{p.first};
                    return Visit(e_i);
                  });
  }
  bool VisitMultiplication(const Expression& e) const {
    const auto& base_to_exponent_map =
        get_base_to_exponent_map_in_multiplication(e);
    return all_of(base_to_exponent_map.begin(), base_to_exponent_map.end(),
                  [this](const pair<const Expression, Expression>& p) {
                    const Expression& base{p.first};
                    const Expression& exponent{p.second};
                    return Visit(base) && Visit(exponent);
                  });
  }
  bool VisitDivision(const Expression& e) const {
    return Visit(get_first_argument(e)) && Visit(get_second_argument(e));
  }
  bool VisitLog(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitAbs(const Expression&) const { return false; }
  bool VisitExp(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitSqrt(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitPow(const Expression& e) const {
    return Visit(get_first_argument(e)) && Visit(get_second_argument(e));
  }
  bool VisitSin(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitCos(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitTan(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitAsin(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitAcos(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitAtan(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitAtan2(const Expression& e) const {
    return Visit(get_first_argument(e)) && Visit(get_second_argument(e));
  }
  bool VisitSinh(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitCosh(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitTanh(const Expression& e) const { return Visit(get_argument(e)); }
  bool VisitMin(const Expression&) const { return false; }
  bool VisitMax(const Expression&) const { return false; }
  bool VisitIfThenElse(const Expression&) const { return false; }
  bool VisitUninterpretedFunction(const Expression&) const { return false; }
  bool VisitIntegral(const Expression&) const { return false; }

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend bool drake::symbolic::VisitFormula<bool>(
      const IsDifferentiableVisitor*, const Formula&);
  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend bool drake::symbolic::VisitExpression<bool>(
      const IsDifferentiableVisitor*, const Expression&);
};

}  // namespace

/// Strengthen the input formula $p f by @p delta.
Formula DeltaStrengthen(const Formula& f, const double delta) {
  DREAL_ASSERT(delta > 0);
  return DeltaStrengthenVisitor{}.Strengthen(f, delta);
}

/// Weaken the input formula $p f by @p delta.
Formula DeltaWeaken(const Formula& f, const double delta) {
  DREAL_ASSERT(delta > 0);
  return DeltaStrengthenVisitor{}.Strengthen(f, -delta);
}

bool IsDifferentiable(const Formula& f) {
  return IsDifferentiableVisitor{}.Visit(f);
}

bool IsDifferentiable(const Expression& e) {
  return IsDifferentiableVisitor{}.Visit(e);
}

Formula make_conjunction(const vector<Formula>& formulas) {
  Formula ret{Formula::True()};
  for (const auto& f_i : formulas) {
    ret = std::move(ret) && f_i;
  }
  return ret;
}

Formula make_disjunction(const vector<Formula>& formulas) {
  Formula ret{Formula::False()};
  for (const auto& f_i : formulas) {
    ret = std::move(ret) || f_i;
  }
  return ret;
}

vector<Variable> CreateVector(const string& prefix, const int size,
                              const Variable::Type type) {
  DREAL_ASSERT(prefix.length() > 0);
  DREAL_ASSERT(size >= 1);
  vector<Variable> v;
  v.reserve(size);
  for (int i = 0; i < size; ++i) {
    v.emplace_back(prefix + to_string(i), type);
  }
  return v;
}

RelationalOperator operator!(const RelationalOperator op) {
  switch (op) {
    case RelationalOperator::EQ:
      return RelationalOperator::NEQ;

    case RelationalOperator::NEQ:
      return RelationalOperator::EQ;

    case RelationalOperator::GT:
      return RelationalOperator::LEQ;

    case RelationalOperator::GEQ:
      return RelationalOperator::LT;

    case RelationalOperator::LT:
      return RelationalOperator::GEQ;

    case RelationalOperator::LEQ:
      return RelationalOperator::GT;
  }
  DREAL_UNREACHABLE();
}

ostream& operator<<(ostream& os, const RelationalOperator op) {
  switch (op) {
    case RelationalOperator::EQ:
      return os << "=";

    case RelationalOperator::NEQ:
      return os << "≠";

    case RelationalOperator::GT:
      return os << ">";

    case RelationalOperator::GEQ:
      return os << "≥";

    case RelationalOperator::LT:
      return os << "<";

    case RelationalOperator::LEQ:
      return os << "≤";
  }
  DREAL_UNREACHABLE();
}

}  // namespace dreal
