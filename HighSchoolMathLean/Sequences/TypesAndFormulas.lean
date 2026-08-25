/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Sequences.Basic

namespace HighSchoolMathLean.Sequences

/-- A finite real sequence of a specified length. -/
abbrev FiniteRealSequence (length : ℕ) := Fin length → ℝ

/-- An infinite real sequence. -/
abbrev InfiniteRealSequence := RealSequence

/-- A sequence is strictly increasing when every later index has a larger
value. -/
def IsIncreasingSequence (a : RealSequence) : Prop :=
  StrictMono a

/-- A sequence is strictly decreasing when every later index has a smaller
value. -/
def IsDecreasingSequence (a : RealSequence) : Prop :=
  StrictAnti a

/-- A sequence is constant when all of its terms equal one fixed real number. -/
def IsConstantSequence (a : RealSequence) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, a n = c

/-- A formula is a general-term formula for a sequence when it computes every
term from its index. -/
def HasGeneralFormula (a formula : RealSequence) : Prop :=
  ∀ n : ℕ, a n = formula n

/-- The alternating reciprocal sequence `1, -1/2, 1/3, -1/4, ...`, written
with zero-based indices. -/
noncomputable def alternatingReciprocalSequence : RealSequence :=
  fun n => (-1 : ℝ) ^ n / (n + 1)

/-- An order-`r` recurrence computes each later term from the preceding `r`
terms. -/
def HasRecurrenceOfOrder
    (a : RealSequence) (r : ℕ) (step : (Fin r → ℝ) → ℝ) : Prop :=
  0 < r ∧ ∀ n : ℕ, a (n + r) = step (fun i => a (n + (i : ℕ)))

/-- A Fibonacci sequence starts with `1, 1` and each later term is the sum of
the preceding two terms. -/
def IsFibonacciSequence (a : RealSequence) : Prop :=
  a 0 = 1 ∧ a 1 = 1 ∧ ∀ n : ℕ, a (n + 2) = a (n + 1) + a n

/-- The sum of the first `n` terms of a zero-based real sequence. -/
noncomputable def partialSum (a : RealSequence) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) a

end HighSchoolMathLean.Sequences
