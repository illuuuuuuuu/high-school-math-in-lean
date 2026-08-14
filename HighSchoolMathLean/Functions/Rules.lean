/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Basic

namespace HighSchoolMathLean.Functions

/-- A real-valued explicit rule assigns the output by evaluating a real function. -/
def IsExplicitRule (f : ℝ → ℝ) (x y : ℝ) : Prop :=
  y = f x

end HighSchoolMathLean.Functions
