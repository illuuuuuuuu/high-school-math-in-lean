/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Trigonometry.AngleIdentities
import Mathlib.Tactic

namespace HighSchoolMathLean.Trigonometry

/-- Convert a sine-cosine product into a sum of sines. -/
theorem sine_mul_cosine_product_to_sum (alpha beta : ℝ) :
    sineFunction alpha * cosineFunction beta =
      (sineFunction (alpha + beta) + sineFunction (alpha - beta)) / 2 := by
  change Real.sin alpha * Real.cos beta =
    (Real.sin (alpha + beta) + Real.sin (alpha - beta)) / 2
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- Convert a cosine-sine product into a difference of sines. -/
theorem cosine_mul_sine_product_to_sum (alpha beta : ℝ) :
    cosineFunction alpha * sineFunction beta =
      (sineFunction (alpha + beta) - sineFunction (alpha - beta)) / 2 := by
  change Real.cos alpha * Real.sin beta =
    (Real.sin (alpha + beta) - Real.sin (alpha - beta)) / 2
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- Convert a cosine-cosine product into a sum of cosines. -/
theorem cosine_mul_cosine_product_to_sum (alpha beta : ℝ) :
    cosineFunction alpha * cosineFunction beta =
      (cosineFunction (alpha + beta) + cosineFunction (alpha - beta)) / 2 := by
  change Real.cos alpha * Real.cos beta =
    (Real.cos (alpha + beta) + Real.cos (alpha - beta)) / 2
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- Convert a sine-sine product into a difference of cosines. -/
theorem sine_mul_sine_product_to_sum (alpha beta : ℝ) :
    sineFunction alpha * sineFunction beta =
      -(cosineFunction (alpha + beta) - cosineFunction (alpha - beta)) / 2 := by
  change Real.sin alpha * Real.sin beta =
    -(Real.cos (alpha + beta) - Real.cos (alpha - beta)) / 2
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- Convert a sum of sines into a product. -/
theorem sine_add_sine_sum_to_product (alpha beta : ℝ) :
    sineFunction alpha + sineFunction beta =
      2 * sineFunction ((alpha + beta) / 2) *
        cosineFunction ((alpha - beta) / 2) := by
  simpa [sineFunction, cosineFunction] using Real.sin_add_sin alpha beta

/-- Convert a difference of sines into a product. -/
theorem sine_sub_sine_sum_to_product (alpha beta : ℝ) :
    sineFunction alpha - sineFunction beta =
      2 * cosineFunction ((alpha + beta) / 2) *
        sineFunction ((alpha - beta) / 2) := by
  change Real.sin alpha - Real.sin beta =
    2 * Real.cos ((alpha + beta) / 2) * Real.sin ((alpha - beta) / 2)
  calc
    Real.sin alpha - Real.sin beta =
        2 * Real.sin ((alpha - beta) / 2) * Real.cos ((alpha + beta) / 2) :=
      Real.sin_sub_sin alpha beta
    _ = 2 * Real.cos ((alpha + beta) / 2) * Real.sin ((alpha - beta) / 2) := by
      ring

/-- Convert a sum of cosines into a product. -/
theorem cosine_add_cosine_sum_to_product (alpha beta : ℝ) :
    cosineFunction alpha + cosineFunction beta =
      2 * cosineFunction ((alpha + beta) / 2) *
        cosineFunction ((alpha - beta) / 2) := by
  simpa [cosineFunction] using Real.cos_add_cos alpha beta

/-- Convert a difference of cosines into a product. -/
theorem cosine_sub_cosine_sum_to_product (alpha beta : ℝ) :
    cosineFunction alpha - cosineFunction beta =
      -2 * sineFunction ((alpha + beta) / 2) *
        sineFunction ((alpha - beta) / 2) := by
  simpa [sineFunction, cosineFunction] using Real.cos_sub_cos alpha beta

/-- Express sine using the tangent of the half-angle. -/
theorem sine_half_angle_substitution (alpha : ℝ)
    (_hhalf : cosineFunction (alpha / 2) ≠ 0) :
    sineFunction alpha =
      2 * tangentFunction (alpha / 2) /
        (1 + tangentFunction (alpha / 2) ^ 2) := by
  simpa [sineFunction, tangentFunction] using
    Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq alpha

/-- Express cosine using the tangent of the half-angle. -/
theorem cosine_half_angle_substitution (alpha : ℝ)
    (hhalf : cosineFunction (alpha / 2) ≠ 0) :
    cosineFunction alpha =
      (1 - tangentFunction (alpha / 2) ^ 2) /
        (1 + tangentFunction (alpha / 2) ^ 2) := by
  have hhalf' : Real.cos (alpha / 2) ≠ 0 := by
    simpa [cosineFunction] using hhalf
  have halpha : Real.cos alpha ≠ -1 := by
    intro h
    rcases Real.cos_eq_neg_one_iff.mp h with ⟨k, hk⟩
    apply hhalf'
    rw [← hk]
    apply Real.cos_eq_zero_iff.mpr
    refine ⟨k, ?_⟩
    ring
  simpa [cosineFunction, tangentFunction] using
    Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq alpha halpha

/-- Express tangent using the tangent of the half-angle. -/
theorem tangent_half_angle_substitution (alpha : ℝ)
    (_halpha : cosineFunction alpha ≠ 0)
    (_hhalf : cosineFunction (alpha / 2) ≠ 0) :
    tangentFunction alpha =
      2 * tangentFunction (alpha / 2) /
        (1 - tangentFunction (alpha / 2) ^ 2) := by
  simpa [tangentFunction] using
    Real.tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq alpha

end HighSchoolMathLean.Trigonometry
