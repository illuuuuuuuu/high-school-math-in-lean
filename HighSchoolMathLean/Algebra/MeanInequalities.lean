/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Algebra.Means
import Mathlib.Tactic

namespace HighSchoolMathLean.Algebra

/-- For nonnegative real numbers, the arithmetic mean is at least the geometric mean,
with equality exactly when the two numbers are equal. -/
theorem arithmetic_mean_ge_geometric_mean {a b : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) :
    geometricMean a b ≤ arithmeticMean a b ∧
      (arithmeticMean a b = geometricMean a b ↔ a = b) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hs : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt hab
  constructor
  · unfold geometricMean arithmeticMean
    nlinarith [sq_nonneg (a - b)]
  · constructor
    · intro heq
      unfold arithmeticMean geometricMean at heq
      nlinarith [sq_nonneg (a - b)]
    · intro heq
      subst b
      unfold arithmeticMean geometricMean
      nlinarith

/-- For nonnegative real numbers, the quadratic mean is at least the arithmetic mean,
with equality exactly when the two numbers are equal. -/
theorem quadratic_mean_ge_arithmetic_mean {a b : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) :
    arithmeticMean a b ≤ quadraticMean a b ∧
      (quadraticMean a b = arithmeticMean a b ↔ a = b) := by
  have hrad : 0 ≤ (a ^ 2 + b ^ 2) / 2 := by positivity
  have hq : 0 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := Real.sqrt_nonneg _
  have hq_sq : (Real.sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 =
      (a ^ 2 + b ^ 2) / 2 := Real.sq_sqrt hrad
  constructor
  · unfold arithmeticMean quadraticMean
    nlinarith [sq_nonneg (a - b)]
  · constructor
    · intro heq
      unfold quadraticMean arithmeticMean at heq
      nlinarith [sq_nonneg (a - b)]
    · intro heq
      subst b
      unfold quadraticMean arithmeticMean
      nlinarith

/-- For positive real numbers, the geometric mean is at least the harmonic mean,
with equality exactly when the two numbers are equal. -/
theorem geometric_mean_ge_harmonic_mean {a b : ℝ} (ha : a > 0) (hb : b > 0) :
    harmonicMean a b ≤ geometricMean a b ∧
      (geometricMean a b = harmonicMean a b ↔ a = b) := by
  have hsum : 0 < a + b := add_pos ha hb
  have hden : 0 < 1 / a + 1 / b := by positivity
  have hhm : harmonicMean a b = 2 * a * b / (a + b) := by
    unfold harmonicMean
    field_simp [ha.ne', hb.ne', hsum.ne', hden.ne']
    <;> ring
  have hgm : 0 ≤ geometricMean a b := by
    exact Real.sqrt_nonneg _
  have hgm_pos : 0 < geometricMean a b := by
    unfold geometricMean
    exact Real.sqrt_pos.2 (mul_pos ha hb)
  have hgm_sq : (geometricMean a b) ^ 2 = a * b := by
    unfold geometricMean
    exact Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have ham := arithmetic_mean_ge_geometric_mean ha.le hb.le
  constructor
  · rw [hhm]
    apply (div_le_iff₀ hsum).2
    have hgap : 0 ≤ a + b - 2 * geometricMean a b := by
      unfold arithmeticMean at ham
      nlinarith [ham.1]
    have hprod : 0 ≤ geometricMean a b *
        (a + b - 2 * geometricMean a b) := mul_nonneg hgm hgap
    nlinarith
  · constructor
    · intro heq
      rw [hhm] at heq
      have heqmul : geometricMean a b * (a + b) = 2 * a * b :=
        (eq_div_iff hsum.ne').mp heq
      apply ham.2.mp
      unfold arithmeticMean
      nlinarith
    · intro heq
      subst b
      unfold geometricMean harmonicMean
      have hs : Real.sqrt (a * a) = a := by
        nlinarith [Real.sq_sqrt (mul_nonneg ha.le ha.le), Real.sqrt_nonneg (a * a)]
      rw [hs]
      field_simp [ha.ne']

/-- The four elementary means of two positive real numbers form the standard chain,
and all adjacent equalities hold exactly when the numbers are equal. -/
theorem positive_mean_inequality_chain {a b : ℝ} (ha : a > 0) (hb : b > 0) :
    harmonicMean a b ≤ geometricMean a b ∧
      geometricMean a b ≤ arithmeticMean a b ∧
      arithmeticMean a b ≤ quadraticMean a b ∧
      ((harmonicMean a b = geometricMean a b ∧
        geometricMean a b = arithmeticMean a b ∧
        arithmeticMean a b = quadraticMean a b) ↔ a = b) := by
  have ham := arithmetic_mean_ge_geometric_mean ha.le hb.le
  have hqm := quadratic_mean_ge_arithmetic_mean ha.le hb.le
  have hgm := geometric_mean_ge_harmonic_mean ha hb
  refine ⟨hgm.1, ham.1, hqm.1, ?_⟩
  constructor
  · intro heq
    exact hgm.2.mp heq.1.symm
  · intro heq
    exact ⟨(hgm.2.mpr heq).symm, (ham.2.mpr heq).symm,
      (hqm.2.mpr heq).symm⟩

/-- The two-dimensional Cauchy--Schwarz inequality over the real numbers,
including its equality condition. -/
theorem cauchy_schwarz_two_dimensional (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ∧
      ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 ↔
        a * d = b * c) := by
  have hid : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) -
      (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by
    ring
  constructor
  · nlinarith [sq_nonneg (a * d - b * c)]
  · constructor
    · intro heq
      nlinarith [sq_nonneg (a * d - b * c)]
    · intro heq
      nlinarith [sq_nonneg (a * d - b * c)]

/-- The addition and subtraction forms of the absolute-value inequality,
including all four equality conditions. -/
theorem abs_add_sub_bounds_with_equality_conditions (a b : ℝ) :
    ((abs (abs a - abs b) ≤ abs (a + b) ∧
        abs (a + b) ≤ abs a + abs b) ∧
      (abs (a + b) = abs a + abs b ↔ 0 ≤ a * b) ∧
      (abs (abs a - abs b) = abs (a + b) ↔ a * b ≤ 0)) ∧
    ((abs (abs a - abs b) ≤ abs (a - b) ∧
        abs (a - b) ≤ abs a + abs b) ∧
      (abs (a - b) = abs a + abs b ↔ a * b ≤ 0) ∧
      (abs (abs a - abs b) = abs (a - b) ↔ 0 ≤ a * b)) := by
  have ha_sq : (abs a) ^ 2 = a ^ 2 := sq_abs a
  have hb_sq : (abs b) ^ 2 = b ^ 2 := sq_abs b
  have hp_mul : abs (a * b) = abs a * abs b := abs_mul a b
  have hlower_sq : (abs (abs a - abs b)) ^ 2 =
      (abs a - abs b) ^ 2 := sq_abs (abs a - abs b)
  have hplus_sq : (abs (a + b)) ^ 2 = (a + b) ^ 2 := sq_abs (a + b)
  have hminus_sq : (abs (a - b)) ^ 2 = (a - b) ^ 2 := sq_abs (a - b)
  have hlower_nonneg : 0 ≤ abs (abs a - abs b) := abs_nonneg _
  have hplus_nonneg : 0 ≤ abs (a + b) := abs_nonneg _
  have hminus_nonneg : 0 ≤ abs (a - b) := abs_nonneg _
  have hsum_nonneg : 0 ≤ abs a + abs b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hp_le_abs : a * b ≤ abs (a * b) := le_abs_self _
  have hnegp_le_abs : -(a * b) ≤ abs (a * b) := neg_le_abs _
  constructor
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · constructor
      · intro heq
        nlinarith
      · intro hp
        have hp_eq : abs (a * b) = a * b := abs_of_nonneg hp
        nlinarith
    · constructor
      · intro heq
        nlinarith
      · intro hp
        have hp_eq : abs (a * b) = -(a * b) := abs_of_nonpos hp
        nlinarith
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · constructor
      · intro heq
        nlinarith
      · intro hp
        have hp_eq : abs (a * b) = -(a * b) := abs_of_nonpos hp
        nlinarith
    · constructor
      · intro heq
        nlinarith
      · intro hp
        have hp_eq : abs (a * b) = a * b := abs_of_nonneg hp
        nlinarith

end HighSchoolMathLean.Algebra
