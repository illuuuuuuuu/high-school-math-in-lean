/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HighSchoolMathLean.Algebra

/-- Comparing two real numbers is equivalent to comparing their difference with zero. -/
theorem real_comparison_by_subtraction (a b : ℝ) :
    (a > b ↔ a - b > 0) ∧
    (a = b ↔ a - b = 0) ∧
    (a < b ↔ a - b < 0) := by
  constructor
  · constructor <;> intro h <;> linarith
  · constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro h <;> linarith

/-- Equality is symmetric. -/
theorem equality_symmetric {α : Type*} {a b : α} (h : a = b) : b = a := by
  exact h.symm

/-- Equality is transitive. -/
theorem equality_transitive {α : Type*} {a b c : α}
    (hab : a = b) (hbc : b = c) : a = c := by
  exact hab.trans hbc

/-- Adding or subtracting the same real number preserves equality. -/
theorem real_add_sub_preserves_equality {a b : ℝ} (c : ℝ) (h : a = b) :
    a + c = b + c ∧ a - c = b - c := by
  subst b
  exact ⟨rfl, rfl⟩

/-- Multiplying equal real numbers by the same factor preserves equality. -/
theorem real_mul_preserves_equality {a b : ℝ} (c : ℝ) (h : a = b) :
    a * c = b * c := by
  rw [h]

end HighSchoolMathLean.Algebra
