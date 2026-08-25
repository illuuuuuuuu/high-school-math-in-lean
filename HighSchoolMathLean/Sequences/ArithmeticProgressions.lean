/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Sequences.TypesAndFormulas

namespace HighSchoolMathLean.Sequences

/-- A real sequence is arithmetic when consecutive differences are all equal
to one real constant. -/
def IsArithmeticProgression (a : RealSequence) : Prop :=
  ∃ d : ℝ, ∀ n : ℕ, a (n + 1) - a n = d

/-- A real number is a common difference of a sequence when every consecutive
difference equals it. -/
def IsCommonDifference (a : RealSequence) (d : ℝ) : Prop :=
  ∀ n : ℕ, a (n + 1) - a n = d

/-- The zero-based general-term formula for an arithmetic progression. -/
theorem arithmetic_progression_general_term
    {a : RealSequence} {d : ℝ} (h : IsCommonDifference a d) (n : ℕ) :
    a n = a 0 + (n : ℝ) * d := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : a (n + 1) = a n + d := by
        linarith [h n]
      rw [hstep, ih]
      push_cast
      ring

end HighSchoolMathLean.Sequences
