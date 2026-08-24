/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.PlaneVectors.LinearAndDirection

namespace HighSchoolMathLean.PlaneVectors

/-- The dot product of two plane vectors is their real Euclidean inner
product. In particular, it is zero when either vector is zero. -/
noncomputable def dotProduct (a b : PlaneVector) : ℝ :=
  inner ℝ a b

/-- The dot product is determined by the two moduli and the angle between the
vectors. -/
theorem dot_product_angle_formula (a b : PlaneVector) :
    dotProduct a b =
      vectorModulus a * vectorModulus b * Real.cos (vectorAngle a b) := by
  simpa [dotProduct, vectorModulus, vectorAngle, mul_comm, mul_left_comm, mul_assoc] using
    (InnerProductGeometry.cos_angle_mul_norm_mul_norm a b).symm

/-- The projection of `a` onto the nonzero direction `b`. -/
noncomputable def vectorProjection (a b : PlaneVector) (_hb : b ≠ 0) : PlaneVector :=
  (dotProduct a b / dotProduct b b) • b

/-- Fundamental metric and directional properties of the dot product. -/
theorem dot_product_properties (a b : PlaneVector) :
    (dotProduct a b = 0 ↔ Perpendicular a b) ∧
      (vectorAngle a b = 0 →
        dotProduct a b = vectorModulus a * vectorModulus b) ∧
      (vectorAngle a b = Real.pi →
        dotProduct a b = -(vectorModulus a * vectorModulus b)) ∧
      dotProduct a a = vectorModulus a ^ 2 ∧
      Real.sqrt (dotProduct a a) = vectorModulus a ∧
      |dotProduct a b| ≤ vectorModulus a * vectorModulus b := by
  constructor
  · simpa [dotProduct, Perpendicular, vectorAngle] using
      (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two a b)
  · constructor
    · intro hangle
      simpa [dotProduct, vectorModulus, vectorAngle] using
        (InnerProductGeometry.inner_eq_mul_norm_of_angle_eq_zero hangle)
    · constructor
      · intro hangle
        simpa [dotProduct, vectorModulus, vectorAngle] using
          (InnerProductGeometry.inner_eq_neg_mul_norm_of_angle_eq_pi hangle)
      · constructor
        · simp [dotProduct, vectorModulus]
        · constructor
          · simp [dotProduct, vectorModulus]
          · simpa [dotProduct, vectorModulus] using abs_real_inner_le_norm a b

/-- The dot product is symmetric, homogeneous in either argument, and
distributive over vector addition. -/
theorem dot_product_operations (lambda : ℝ) (a b c : PlaneVector) :
    dotProduct a b = dotProduct b a ∧
      dotProduct (lambda • a) b = lambda * dotProduct a b ∧
      dotProduct a (lambda • b) = lambda * dotProduct a b ∧
      dotProduct (a + b) c = dotProduct a c + dotProduct b c := by
  simp [dotProduct, real_inner_comm, real_inner_smul_right,
    inner_add_left]

/-- In the real Euclidean plane, two vectors form a basis precisely when they
are linearly independent. -/
def IsPlaneBasis (e₁ e₂ : PlaneVector) : Prop :=
  LinearIndependent ℝ ![e₁, e₂]

/-- Two nonparallel plane vectors form a basis of the plane. -/
theorem nonparallel_isPlaneBasis {e₁ e₂ : PlaneVector}
    (h : ¬ Parallel e₁ e₂) : IsPlaneBasis e₁ e₂ := by
  rw [IsPlaneBasis]
  by_contra hdependent
  apply h
  exact sameRay_or_sameRay_neg_iff_not_linearIndependent.mpr hdependent

/-- A scalar expression is a decomposition of `a` in `e₁,e₂` exactly when
it evaluates to `a`. -/
def IsDecomposition (a e₁ e₂ : PlaneVector) (lambda mu : ℝ) : Prop :=
  a = lambda • e₁ + mu • e₂

/-- A decomposition is orthogonal when its two direction vectors are
perpendicular. -/
def IsOrthogonalDecomposition
    (a e₁ e₂ : PlaneVector) (lambda mu : ℝ) : Prop :=
  IsDecomposition a e₁ e₂ lambda mu ∧ Perpendicular e₁ e₂

/-- Coordinate decomposition in the standard orthonormal basis of the real
Euclidean plane. -/
noncomputable def IsCoordinateDecomposition (a : PlaneVector) (x y : ℝ) : Prop :=
  a = x • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    y • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

end HighSchoolMathLean.PlaneVectors
