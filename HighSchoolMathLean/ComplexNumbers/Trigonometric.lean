/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.ComplexNumbers.GeometryAndOperations
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace HighSchoolMathLean.ComplexNumbers

open ComplexConjugate

/-- Nonzero complex numbers satisfy the commutative-group laws for
multiplication; their inverse is obtained from conjugation and squared
modulus. -/
theorem complex_multiplicative_group_properties (z₁ z₂ z₃ : ℂ) :
    z₁ * z₂ = z₂ * z₁ ∧
      (z₁ * z₂) * z₃ = z₁ * (z₂ * z₃) ∧
      z₁ * 1 = z₁ ∧
      (∀ z : ℂ, z ≠ 0 →
        z * z⁻¹ = 1 ∧
          z⁻¹ = conj z * ((‖z‖ ^ 2)⁻¹ : ℝ)) ∧
      z₁ * z₂ ∈ complexSet := by
  refine ⟨mul_comm _ _, mul_assoc _ _ _, by simp, ?_, ?_⟩
  · intro z hz
    constructor
    · exact Complex.mul_inv_cancel hz
    · rw [Complex.inv_def, Complex.normSq_eq_norm_sq]
  · exact ⟨(z₁ * z₂).re, (z₁ * z₂).im, by apply Complex.ext <;> rfl⟩

/-- Division of complex numbers in real and imaginary coordinates. -/
theorem complex_div_formula (a b c d : ℝ)
    (h₂ : complexNumber c d ≠ 0) :
    complexNumber a b / complexNumber c d =
      complexNumber ((a * c + b * d) / (c ^ 2 + d ^ 2))
        ((b * c - a * d) / (c ^ 2 + d ^ 2)) := by
  have hden : c ^ 2 + d ^ 2 ≠ 0 := by
    intro hzero
    have hc : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    apply h₂
    apply Complex.ext <;> simp [complexNumber, hc, hd]
  apply Complex.ext
  · simp [complexNumber, Complex.div_re, Complex.normSq_apply, pow_two]
    field_simp [hden]
  · simp [complexNumber, Complex.div_im, Complex.normSq_apply, pow_two]
    field_simp [hden]

/-- An argument of a nonzero complex number is an angle giving its unit
direction in polar form. -/
def IsArgument (z : ℂ) (theta : ℝ) : Prop :=
  z ≠ 0 ∧
    z = ‖z‖ * (Real.cos theta + Real.sin theta * Complex.I)

/-- The principal argument in the interval `[0, 2π)`, obtained from
Mathlib's argument in `(-π, π]`. -/
noncomputable def principalArgument (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

/-- Every complex number has its standard polar representation using its
modulus and Mathlib's argument. -/
theorem complex_trigonometric_representation (z : ℂ) :
    z = ‖z‖ *
      (Real.cos (Complex.arg z) + Real.sin (Complex.arg z) * Complex.I) := by
  rw [← Complex.norm_mul_cos_add_sin_mul_I z]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

/-- Multiplication in polar form multiplies moduli and adds arguments. -/
theorem complex_mul_trigonometric
    {z₁ z₂ : ℂ} {r₁ r₂ theta₁ theta₂ : ℝ}
    (h₁ : z₁ = r₁ * (Real.cos theta₁ + Real.sin theta₁ * Complex.I))
    (h₂ : z₂ = r₂ * (Real.cos theta₂ + Real.sin theta₂ * Complex.I)) :
    z₁ * z₂ =
      (r₁ * r₂) *
        (Real.cos (theta₁ + theta₂) +
          Real.sin (theta₁ + theta₂) * Complex.I) := by
  rw [h₁, h₂]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Real.cos_add, Real.sin_add] <;> ring

/-- Division in polar form divides moduli and subtracts arguments. -/
theorem complex_div_trigonometric
    {z₁ z₂ : ℂ} {r₁ r₂ theta₁ theta₂ : ℝ}
    (hr₂ : r₂ ≠ 0)
    (h₁ : z₁ = r₁ * (Real.cos theta₁ + Real.sin theta₁ * Complex.I))
    (h₂ : z₂ = r₂ * (Real.cos theta₂ + Real.sin theta₂ * Complex.I)) :
    z₁ / z₂ =
      (r₁ / r₂) *
        (Real.cos (theta₁ - theta₂) +
          Real.sin (theta₁ - theta₂) * Complex.I) := by
  rw [h₁, h₂]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Real.cos_sub, Real.sin_sub] <;>
    field_simp [hr₂] <;>
    rw [Real.cos_sq_add_sin_sq] <;>
    ring

end HighSchoolMathLean.ComplexNumbers
