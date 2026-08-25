/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.ComplexNumbers.Basic
import HighSchoolMathLean.PlaneVectors.Coordinates
import Mathlib.Analysis.Complex.Norm

namespace HighSchoolMathLean.ComplexNumbers

open ComplexConjugate

/-- Complex numbers with zero imaginary part form a proper subset of all
complex numbers. -/
theorem real_numbers_proper_subset_complexSet :
    {z : ℂ | imaginaryPart z = 0} ⊂ complexSet := by
  rw [Set.ssubset_iff_exists]
  constructor
  · intro z _hz
    exact ⟨z.re, z.im, by apply Complex.ext <;> rfl⟩
  · refine ⟨Complex.I, ?_, ?_⟩
    · exact ⟨0, 1, by apply Complex.ext <;> simp [complexNumber]⟩
    · simp [imaginaryPart]

/-- The complex plane is identified with the real coordinate plane by real
and imaginary parts. -/
noncomputable def complexPlaneEquiv : ℂ ≃ ℝ × ℝ where
  toFun z := (z.re, z.im)
  invFun p := complexNumber p.1 p.2
  left_inv z := by apply Complex.ext <;> rfl
  right_inv p := by rcases p with ⟨x, y⟩; rfl

/-- Complex numbers correspond bijectively both to points of the real plane
and to plane vectors based at the origin. -/
theorem complex_geometric_correspondences :
    Function.Bijective (fun z : ℂ => (z.re, z.im)) ∧
      Function.Bijective (fun z : ℂ =>
        PlaneVectors.coordinateVector z.re z.im) := by
  constructor
  · exact complexPlaneEquiv.bijective
  · constructor
    · intro z w h
      apply Complex.ext
      · have h₀ := congrArg (fun v : PlaneVectors.PlaneVector => v 0) h
        simpa [PlaneVectors.coordinateVector] using h₀
      · have h₁ := congrArg (fun v : PlaneVectors.PlaneVector => v 1) h
        simpa [PlaneVectors.coordinateVector] using h₁
    · intro v
      refine ⟨complexNumber (v 0) (v 1), ?_⟩
      ext i
      fin_cases i <;> simp [complexNumber, PlaneVectors.coordinateVector]

/-- The modulus of `a + bi` is `sqrt (a² + b²)`. -/
theorem complex_modulus_formula (a b : ℝ) :
    ‖complexNumber a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  simp [Complex.norm_def, Complex.normSq_apply, complexNumber, pow_two]

/-- On complex numbers coming from the real axis, the complex modulus agrees
with the real absolute value. -/
theorem real_complex_modulus (a : ℝ) :
    ‖complexNumber a 0‖ = |a| := by
  rw [complex_modulus_formula]
  simp [Real.sqrt_sq_eq_abs]

/-- Complex conjugation sends `a + bi` to `a - bi`; when `b` is nonzero the
two conjugates are both imaginary. -/
theorem complex_conjugate_formula (a b : ℝ) :
    conj (complexNumber a b) = complexNumber a (-b) ∧
      (b ≠ 0 →
        IsImaginary (complexNumber a b) ∧
          IsImaginary (conj (complexNumber a b))) := by
  constructor
  · apply Complex.ext <;> simp [complexNumber]
  · intro hb
    constructor <;> simpa [IsImaginary, imaginaryPart, complexNumber] using hb

/-- Addition of complex numbers is coordinatewise. -/
theorem complex_add_formula (a b c d : ℝ) :
    complexNumber a b + complexNumber c d = complexNumber (a + c) (b + d) := by
  apply Complex.ext <;> simp [complexNumber]

/-- Complex addition is commutative and associative, has zero and additive
inverses, and is closed in the set of complex numbers. -/
theorem complex_additive_group_properties (z₁ z₂ z₃ : ℂ) :
    z₁ + z₂ = z₂ + z₁ ∧
      (z₁ + z₂) + z₃ = z₁ + (z₂ + z₃) ∧
      z₁ + 0 = z₁ ∧
      z₁ + (-z₁) = 0 ∧
      z₁ + z₂ ∈ complexSet := by
  refine ⟨add_comm _ _, add_assoc _ _ _, by simp, by simp, ?_⟩
  exact ⟨(z₁ + z₂).re, (z₁ + z₂).im, by apply Complex.ext <;> rfl⟩

/-- Subtraction of complex numbers is coordinatewise. -/
theorem complex_sub_formula (a b c d : ℝ) :
    complexNumber a b - complexNumber c d = complexNumber (a - c) (b - d) := by
  apply Complex.ext <;> simp [complexNumber]

/-- Multiplication of complex numbers follows the usual real-coordinate
formula. -/
theorem complex_mul_formula (a b c d : ℝ) :
    complexNumber a b * complexNumber c d =
      complexNumber (a * c - b * d) (a * d + b * c) := by
  apply Complex.ext <;> simp [complexNumber, Complex.mul_re, Complex.mul_im]

end HighSchoolMathLean.ComplexNumbers
