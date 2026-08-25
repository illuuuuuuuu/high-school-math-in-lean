/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Tactic

namespace HighSchoolMathLean.Sequences

/-- A real sequence is a real-valued function on the natural numbers. The
value at index `0` represents the first term. -/
abbrev RealSequence := ℕ → ℝ

/-- The term of a sequence at a specified zero-based index. -/
def sequenceTerm (a : RealSequence) (n : ℕ) : ℝ :=
  a n

end HighSchoolMathLean.Sequences
