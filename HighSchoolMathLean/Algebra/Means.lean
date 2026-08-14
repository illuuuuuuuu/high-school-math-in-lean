/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Sqrt

namespace HighSchoolMathLean.Algebra

/-- The arithmetic mean of two real numbers. -/
noncomputable def arithmeticMean (a b : ℝ) : ℝ :=
  (a + b) / 2

/-- The geometric mean of two real numbers. -/
noncomputable def geometricMean (a b : ℝ) : ℝ :=
  Real.sqrt (a * b)

/-- The harmonic mean of two real numbers. -/
noncomputable def harmonicMean (a b : ℝ) : ℝ :=
  2 / (1 / a + 1 / b)

/-- The quadratic mean of two real numbers. -/
noncomputable def quadraticMean (a b : ℝ) : ℝ :=
  Real.sqrt ((a ^ 2 + b ^ 2) / 2)

end HighSchoolMathLean.Algebra
