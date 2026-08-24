/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Trigonometry.QualitativeProperties
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace HighSchoolMathLean.Trigonometry

/-- On its central branch, tangent takes every real value. Consequently, its
range on the real line is also all of `ℝ`. -/
theorem tangentFunction_range :
    tangentFunction '' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) = Set.univ := by
  simpa [tangentFunction] using Real.image_tan_Ioo

/-- The cosine addition and subtraction identities. -/
theorem cosine_add_subtract (alpha beta : ℝ) :
    cosineFunction (alpha + beta) =
        cosineFunction alpha * cosineFunction beta -
          sineFunction alpha * sineFunction beta ∧
    cosineFunction (alpha - beta) =
        cosineFunction alpha * cosineFunction beta +
          sineFunction alpha * sineFunction beta := by
  exact ⟨by simpa [cosineFunction, sineFunction] using Real.cos_add alpha beta,
    by simpa [cosineFunction, sineFunction] using Real.cos_sub alpha beta⟩

/-- The sine addition and subtraction identities. -/
theorem sine_add_subtract (alpha beta : ℝ) :
    sineFunction (alpha + beta) =
        sineFunction alpha * cosineFunction beta +
          cosineFunction alpha * sineFunction beta ∧
    sineFunction (alpha - beta) =
        sineFunction alpha * cosineFunction beta -
          cosineFunction alpha * sineFunction beta := by
  exact ⟨by simpa [sineFunction, cosineFunction] using Real.sin_add alpha beta,
    by simpa [sineFunction, cosineFunction] using Real.sin_sub alpha beta⟩

/-- The tangent addition and subtraction identities, assuming the two input
tangents are defined in the usual real-variable sense. -/
theorem tangent_add_subtract (alpha beta : ℝ)
    (halpha : cosineFunction alpha ≠ 0)
    (hbeta : cosineFunction beta ≠ 0) :
    tangentFunction (alpha + beta) =
        (tangentFunction alpha + tangentFunction beta) /
          (1 - tangentFunction alpha * tangentFunction beta) ∧
    tangentFunction (alpha - beta) =
        (tangentFunction alpha - tangentFunction beta) /
          (1 + tangentFunction alpha * tangentFunction beta) := by
  have halpha' : ∀ k : ℤ,
      alpha ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 :=
    Real.cos_ne_zero_iff.mp (by simpa [cosineFunction] using halpha)
  have hbeta' : ∀ k : ℤ,
      beta ≠ (2 * (k : ℝ) + 1) * Real.pi / 2 :=
    Real.cos_ne_zero_iff.mp (by simpa [cosineFunction] using hbeta)
  exact ⟨by simpa [tangentFunction] using Real.tan_add' ⟨halpha', hbeta'⟩,
    by simpa [tangentFunction] using Real.tan_sub' ⟨halpha', hbeta'⟩⟩

/-- The three standard forms of the cosine double-angle identity. -/
theorem cosine_double_angle (alpha : ℝ) :
    cosineFunction (2 * alpha) =
        cosineFunction alpha ^ 2 - sineFunction alpha ^ 2 ∧
    cosineFunction (2 * alpha) = 2 * cosineFunction alpha ^ 2 - 1 ∧
    cosineFunction (2 * alpha) = 1 - 2 * sineFunction alpha ^ 2 := by
  exact ⟨by simpa [cosineFunction, sineFunction] using Real.cos_two_mul' alpha,
    by simpa [cosineFunction] using Real.cos_two_mul alpha,
    by simpa [cosineFunction, sineFunction] using
      Real.cos_two_mul_eq_one_sub alpha⟩

/-- The sine double-angle identity. -/
theorem sine_double_angle (alpha : ℝ) :
    sineFunction (2 * alpha) =
      2 * cosineFunction alpha * sineFunction alpha := by
  rw [sineFunction, cosineFunction, Real.sin_two_mul]
  ring

/-- The tangent double-angle identity, with the usual definedness hypotheses
for the two tangent values appearing in the statement. -/
theorem tangent_double_angle (alpha : ℝ)
    (_halpha : cosineFunction alpha ≠ 0)
    (_hdouble : cosineFunction (2 * alpha) ≠ 0) :
    tangentFunction (2 * alpha) =
      2 * tangentFunction alpha / (1 - tangentFunction alpha ^ 2) := by
  simpa [tangentFunction] using Real.tan_two_mul (x := alpha)

/-- The squared cosine half-angle identity. -/
theorem cosine_half_angle_square (alpha : ℝ) :
    cosineFunction (alpha / 2) ^ 2 =
      (1 + cosineFunction alpha) / 2 := by
  change Real.cos (alpha / 2) ^ 2 = (1 + Real.cos alpha) / 2
  have h := Real.cos_sq (alpha / 2)
  rw [show 2 * (alpha / 2) = alpha by ring] at h
  linarith

/-- The squared sine half-angle identity. -/
theorem sine_half_angle_square (alpha : ℝ) :
    sineFunction (alpha / 2) ^ 2 =
      (1 - cosineFunction alpha) / 2 := by
  change Real.sin (alpha / 2) ^ 2 = (1 - Real.cos alpha) / 2
  have h := Real.sin_sq_eq_half_sub (alpha / 2)
  rw [show 2 * (alpha / 2) = alpha by ring] at h
  linarith

/-- The squared tangent half-angle identity, with the usual definedness
hypotheses for `tan alpha` and `tan (alpha / 2)`. -/
theorem tangent_half_angle_square (alpha : ℝ)
    (_halpha : cosineFunction alpha ≠ 0)
    (hhalf : cosineFunction (alpha / 2) ≠ 0) :
    tangentFunction (alpha / 2) ^ 2 =
      (1 - cosineFunction alpha) / (1 + cosineFunction alpha) := by
  change Real.tan (alpha / 2) ^ 2 =
    (1 - Real.cos alpha) / (1 + Real.cos alpha)
  have hhalf' : Real.cos (alpha / 2) ≠ 0 := by
    simpa [cosineFunction] using hhalf
  have hdouble := Real.cos_two_mul (alpha / 2)
  rw [show 2 * (alpha / 2) = alpha by ring] at hdouble
  have hden : 1 + Real.cos alpha ≠ 0 := by
    have hsq : 0 < Real.cos (alpha / 2) ^ 2 := sq_pos_of_ne_zero hhalf'
    nlinarith
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hhalf', hden]
  nlinarith [Real.sin_sq_add_cos_sq (alpha / 2)]

end HighSchoolMathLean.Trigonometry
