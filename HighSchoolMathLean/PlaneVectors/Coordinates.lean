/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.PlaneVectors.InnerProductAndBasis

namespace HighSchoolMathLean.PlaneVectors

/-- The plane vector represented by the ordered pair `(x, y)` in the standard
orthonormal coordinate system. -/
noncomputable def coordinateVector (x y : ℝ) : PlaneVector :=
  !₂[x, y]

/-- Addition and subtraction of plane vectors are coordinatewise. -/
theorem coordinate_vector_add_sub (x₁ y₁ x₂ y₂ : ℝ) :
    coordinateVector x₁ y₁ + coordinateVector x₂ y₂ =
        coordinateVector (x₁ + x₂) (y₁ + y₂) ∧
      coordinateVector x₁ y₁ - coordinateVector x₂ y₂ =
        coordinateVector (x₁ - x₂) (y₁ - y₂) := by
  constructor <;> ext i <;> fin_cases i <;> simp [coordinateVector]

/-- Scalar multiplication of a plane vector is coordinatewise. -/
theorem coordinate_vector_smul (lambda x y : ℝ) :
    lambda • coordinateVector x y = coordinateVector (lambda * x) (lambda * y) := by
  ext i
  fin_cases i <;> simp [coordinateVector]

/-- The Euclidean modulus of a coordinate vector. -/
theorem coordinate_vector_modulus (x y : ℝ) :
    vectorModulus (coordinateVector x y) = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [vectorModulus, EuclideanSpace.norm_eq]
  simp [coordinateVector, Fin.sum_univ_two]

/-- The dot product of coordinate vectors is the sum of the products of their
corresponding coordinates. -/
theorem coordinate_vector_dot_product (x₁ y₁ x₂ y₂ : ℝ) :
    dotProduct (coordinateVector x₁ y₁) (coordinateVector x₂ y₂) =
      x₁ * x₂ + y₁ * y₂ := by
  simp [dotProduct, coordinateVector, PiLp.inner_apply, Fin.sum_univ_two,
    real_inner_eq_re_inner, RCLike.inner_apply]
  all_goals ring

/-- The coordinate formula for the cosine of the angle between two nonzero
plane vectors. -/
theorem coordinate_vector_angle_cos
    (x₁ y₁ x₂ y₂ : ℝ)
    (_h₁ : coordinateVector x₁ y₁ ≠ 0)
    (_h₂ : coordinateVector x₂ y₂ ≠ 0) :
    Real.cos (vectorAngle (coordinateVector x₁ y₁) (coordinateVector x₂ y₂)) =
        dotProduct (coordinateVector x₁ y₁) (coordinateVector x₂ y₂) /
          (vectorModulus (coordinateVector x₁ y₁) *
            vectorModulus (coordinateVector x₂ y₂)) ∧
      dotProduct (coordinateVector x₁ y₁) (coordinateVector x₂ y₂) /
          (vectorModulus (coordinateVector x₁ y₁) *
            vectorModulus (coordinateVector x₂ y₂)) =
        (x₁ * x₂ + y₁ * y₂) /
          (Real.sqrt (x₁ ^ 2 + y₁ ^ 2) * Real.sqrt (x₂ ^ 2 + y₂ ^ 2)) := by
  constructor
  · simpa [dotProduct, vectorModulus, vectorAngle] using
      (InnerProductGeometry.cos_angle
        (coordinateVector x₁ y₁) (coordinateVector x₂ y₂))
  · rw [coordinate_vector_dot_product, coordinate_vector_modulus,
      coordinate_vector_modulus]

/-- Two coordinate vectors are perpendicular exactly when their coordinate
products sum to zero. -/
theorem coordinate_vector_perpendicular_iff (x₁ y₁ x₂ y₂ : ℝ) :
    Perpendicular (coordinateVector x₁ y₁) (coordinateVector x₂ y₂) ↔
      x₁ * x₂ + y₁ * y₂ = 0 := by
  rw [← coordinate_vector_dot_product]
  exact (dot_product_properties
    (coordinateVector x₁ y₁) (coordinateVector x₂ y₂)).1.symm

/-- Two coordinate vectors are parallel exactly when their two-dimensional
determinant is zero. -/
theorem coordinate_vector_parallel_iff (x₁ y₁ x₂ y₂ : ℝ) :
    Parallel (coordinateVector x₁ y₁) (coordinateVector x₂ y₂) ↔
      x₁ * y₂ = x₂ * y₁ := by
  constructor
  · intro hparallel
    by_cases hzero : coordinateVector x₁ y₁ = 0
    · have hx : x₁ = 0 := by
        have := congrArg (fun v : PlaneVector => v 0) hzero
        simpa [coordinateVector] using this
      have hy : y₁ = 0 := by
        have := congrArg (fun v : PlaneVector => v 1) hzero
        simpa [coordinateVector] using this
      simp [hx, hy]
    · obtain ⟨lambda, hlambda, _⟩ :=
        (parallel_iff_existsUnique_smul hzero).mp hparallel
      have hx := congrArg (fun v : PlaneVector => v 0) hlambda
      have hy := congrArg (fun v : PlaneVector => v 1) hlambda
      simp [coordinateVector] at hx hy
      calc
        x₁ * y₂ = x₁ * (lambda * y₁) := by rw [hy]
        _ = (lambda * x₁) * y₁ := by ring
        _ = x₂ * y₁ := by rw [hx]
  · intro hdet
    by_cases hx₁ : x₁ = 0
    · by_cases hy₁ : y₁ = 0
      · subst x₁
        subst y₁
        have hzero : coordinateVector 0 0 = 0 := by
          ext i
          fin_cases i <;> simp [coordinateVector]
        rw [hzero]
        exact zero_parallel (coordinateVector x₂ y₂)
      · have hx₂ : x₂ = 0 := by
          have hproduct : x₂ * y₁ = 0 := by
            rw [hx₁] at hdet
            simpa using hdet.symm
          exact (mul_eq_zero.mp hproduct).resolve_right hy₁
        have hsmul : coordinateVector x₂ y₂ =
            (y₂ / y₁) • coordinateVector x₁ y₁ := by
          ext i
          fin_cases i
          · simp [coordinateVector, hx₁, hx₂]
          · simp [coordinateVector]
            field_simp [hy₁]
        rw [hsmul]
        exact scalar_multiple_parallel (y₂ / y₁) (coordinateVector x₁ y₁)
    · have hsmul : coordinateVector x₂ y₂ =
          (x₂ / x₁) • coordinateVector x₁ y₁ := by
        ext i
        fin_cases i
        · simp [coordinateVector]
          field_simp [hx₁]
        · simp [coordinateVector]
          field_simp [hx₁]
          nlinarith [hdet]
      rw [hsmul]
      exact scalar_multiple_parallel (x₂ / x₁) (coordinateVector x₁ y₁)

end HighSchoolMathLean.PlaneVectors
