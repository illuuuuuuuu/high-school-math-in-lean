/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HighSchoolMathLean.Algebra

/-- Dividing equal real numbers by the same nonzero number preserves equality. -/
theorem real_div_preserves_equality {a b c : ℝ} (h : a = b) (_hc : c ≠ 0) :
    a / c = b / c := by
  subst b
  rfl

/-- Reversing a strict comparison exchanges greater-than and less-than. -/
theorem real_strict_order_symmetry (a b : ℝ) : a > b ↔ b < a := by
  rfl

/-- Strict inequalities between real numbers are transitive. -/
theorem real_strict_order_transitive {a b c : ℝ} (hab : a > b) (hbc : b > c) :
    a > c := by
  exact lt_trans hbc hab

/-- Adding the same real number to both sides preserves a strict inequality. -/
theorem real_add_preserves_strict_order {a b : ℝ} (c : ℝ) (hab : a > b) :
    a + c > b + c := by
  linarith

/-- Multiplication preserves or reverses strict order according to the factor's sign. -/
theorem real_mul_strict_order_by_sign {a b c : ℝ} (hab : a > b) :
    (c > 0 → a * c > b * c) ∧ (c < 0 → a * c < b * c) := by
  constructor
  · intro hc
    exact mul_lt_mul_of_pos_right hab hc
  · intro hc
    exact mul_lt_mul_of_neg_right hab hc

/-- Strict inequalities with the same orientation can be added. -/
theorem real_add_strict_inequalities {a b c d : ℝ} (hab : a > b) (hcd : c > d) :
    a + c > b + d := by
  linarith

/-- Strict inequalities between positive real numbers can be multiplied. -/
theorem real_mul_positive_strict_inequalities {a b c d : ℝ}
    (hab : a > b) (hb : b > 0) (hcd : c > d) (hd : d > 0) :
    a * c > b * d := by
  have hbc : b * c > b * d := mul_lt_mul_of_pos_left hcd hb
  have hac : a * c > b * c := mul_lt_mul_of_pos_right hab (lt_trans hd hcd)
  exact lt_trans hbc hac

/-- Raising positive real numbers to a natural power of at least two preserves strict order. -/
theorem real_pow_preserves_positive_strict_order {a b : ℝ} (n : ℕ)
    (hab : a > b) (hb : b > 0) (hn : n ≥ 2) :
    a ^ n > b ^ n := by
  have ha : a > 0 := lt_trans hb hab
  have hpow : ∀ m : ℕ, a ^ (m + 1) > b ^ (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hab
    | succ m ih =>
        have hbpow : b ^ (m + 1) > 0 := pow_pos hb _
        have hapow : a ^ (m + 1) > 0 := pow_pos ha _
        have hleft : a ^ (m + 1) * b > b ^ (m + 1) * b :=
          mul_lt_mul_of_pos_right ih hb
        have hright : a ^ (m + 1) * a > a ^ (m + 1) * b :=
          mul_lt_mul_of_pos_left hab hapow
        have hstep : a ^ (m + 1) * a > b ^ (m + 1) * b :=
          lt_trans hleft hright
        simpa [pow_succ, Nat.succ_eq_add_one, Nat.add_assoc] using hstep
  let m := n - 1
  have hn_eq : n = m + 1 := by
    dsimp [m]
    omega
  rw [hn_eq]
  exact hpow m

end HighSchoolMathLean.Algebra
