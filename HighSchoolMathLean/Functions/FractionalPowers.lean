/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Functions.PeriodicityAndRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HighSchoolMathLean.Functions

/-- An odd root of an odd power recovers the base, while an even root of an
even power recovers its absolute value. The conclusion is expressed with the
root relation, so it does not choose an arbitrary root of an even power. -/
theorem nth_root_of_nth_power (a : ℝ) (n p : ℕ) :
    (n = 2 * p + 1 → IsNthRoot n a (a ^ n)) ∧
    (n = 2 * p → IsNthRoot n |a| (a ^ n)) := by
  constructor
  · intro _
    rfl
  · intro hn
    rw [IsNthRoot]
    calc
      |a| ^ n = |a| ^ (2 * p) := by rw [hn]
      _ = (|a| ^ 2) ^ p := by rw [pow_mul]
      _ = (a ^ 2) ^ p := by rw [sq_abs]
      _ = a ^ (2 * p) := by rw [pow_mul]
      _ = a ^ n := by rw [hn]

/-- The nonnegative-base interpretation of a positive fractional power. -/
def positiveFractionalPower (a : ℝ) (m n : ℕ) : ℝ :=
  Real.rpow a ((m : ℝ) / (n : ℝ))

/-- A negative fractional power is the reciprocal of the corresponding
positive fractional power. -/
def negativeFractionalPower (a : ℝ) (m n : ℕ) : ℝ :=
  (positiveFractionalPower a m n)⁻¹

/-- Zero raised to a genuinely positive fractional exponent is zero. -/
theorem zero_positive_fractional_power (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    positiveFractionalPower 0 m n = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  exact Real.zero_rpow (div_ne_zero hm0 hn0)

/-- Multiplication law for positive bases and rational exponents. -/
theorem rational_rpow_add (a : ℝ) (r s : ℚ) (ha : 0 < a) :
    Real.rpow a (r : ℝ) * Real.rpow a (s : ℝ) =
      Real.rpow a ((r + s : ℚ) : ℝ) := by
  simpa using (Real.rpow_add ha (r : ℝ) (s : ℝ)).symm

/-- Power-of-a-power law for positive bases and rational exponents. -/
theorem rational_rpow_mul (a : ℝ) (r s : ℚ) (ha : 0 < a) :
    Real.rpow (Real.rpow a (r : ℝ)) (s : ℝ) =
      Real.rpow a ((r * s : ℚ) : ℝ) := by
  simpa using (Real.rpow_mul ha.le (r : ℝ) (s : ℝ)).symm

/-- Product law for positive factors and a rational exponent. -/
theorem rational_mul_rpow (a b : ℝ) (r : ℚ) (ha : 0 < a) (hb : 0 < b) :
    Real.rpow (a * b) (r : ℝ) =
      Real.rpow a (r : ℝ) * Real.rpow b (r : ℝ) := by
  exact Real.mul_rpow ha.le hb.le

/-- Multiplication law for positive bases and real exponents. -/
theorem real_rpow_add (a r s : ℝ) (ha : 0 < a) :
    Real.rpow a r * Real.rpow a s = Real.rpow a (r + s) := by
  exact (Real.rpow_add ha r s).symm

/-- Power-of-a-power law for positive bases and real exponents. -/
theorem real_rpow_mul (a r s : ℝ) (ha : 0 < a) :
    Real.rpow (Real.rpow a r) s = Real.rpow a (r * s) := by
  exact (Real.rpow_mul ha.le r s).symm

/-- Product law for positive factors and a real exponent. -/
theorem real_mul_rpow (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.rpow (a * b) r = Real.rpow a r * Real.rpow b r := by
  exact Real.mul_rpow ha.le hb.le

end HighSchoolMathLean.Functions
