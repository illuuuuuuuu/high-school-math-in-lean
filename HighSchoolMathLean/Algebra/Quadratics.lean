/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Basic

namespace HighSchoolMathLean.Algebra

/-- A quadratic equation over the real numbers, with a nonzero leading coefficient. -/
structure QuadraticEquation where
  a : ℝ
  b : ℝ
  c : ℝ
  leading_ne_zero : a ≠ 0

/-- A real number is a root of a quadratic equation when it makes its polynomial zero. -/
def QuadraticEquation.IsRoot (q : QuadraticEquation) (x : ℝ) : Prop :=
  q.a * x ^ 2 + q.b * x + q.c = 0

end HighSchoolMathLean.Algebra
