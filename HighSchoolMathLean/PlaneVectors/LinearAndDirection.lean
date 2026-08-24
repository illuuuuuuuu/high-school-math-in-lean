/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.PlaneVectors.Operations
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

namespace HighSchoolMathLean.PlaneVectors

/-- Scalar multiplication is associative and distributes over scalar and
vector addition. -/
theorem scalar_multiplication_properties (lambda mu : ℝ) (a b : PlaneVector) :
    lambda • (mu • a) = (lambda * mu) • a ∧
      (lambda + mu) • a = lambda • a + mu • a ∧
      lambda • (a + b) = lambda • a + lambda • b := by
  simp [mul_smul, add_smul, smul_add]

/-- Scalar multiplication respects negation and vector subtraction. -/
theorem special_scalar_properties (lambda : ℝ) (a b : PlaneVector) :
    (-lambda) • a = -(lambda • a) ∧
      -(lambda • a) = lambda • (-a) ∧
      lambda • (a - b) = lambda • a - lambda • b := by
  simp [smul_sub]

/-- A two-vector linear operation has the form `lambda • a + mu • b`. -/
noncomputable def linearOperation
    (lambda mu : ℝ) (a b : PlaneVector) : PlaneVector :=
  lambda • a + mu • b

/-- Scaling a sum or difference of two scalar multiples distributes through
the entire expression. -/
theorem linear_operation_distributive
    (lambda mu₁ mu₂ : ℝ) (a b : PlaneVector) :
    lambda • (mu₁ • a + mu₂ • b) =
        (lambda * mu₁) • a + (lambda * mu₂) • b ∧
      lambda • (mu₁ • a - mu₂ • b) =
        (lambda * mu₁) • a - (lambda * mu₂) • b := by
  simp [smul_add, smul_sub, mul_smul]

/-- A nonzero vector is parallel to another vector exactly when the latter is
a unique real scalar multiple of the former. -/
theorem parallel_iff_existsUnique_smul {a b : PlaneVector} (ha : a ≠ 0) :
    Parallel a b ↔ ∃! lambda : ℝ, b = lambda • a := by
  constructor
  · intro hab
    rcases hab with hab | hab
    · obtain ⟨lambda, _hlambda, hlambda⟩ := hab.exists_nonneg_left ha
      refine ⟨lambda, hlambda.symm, ?_⟩
      intro mu hmu
      exact smul_left_injective ℝ ha (hmu.symm.trans hlambda.symm)
    · obtain ⟨lambda, _hlambda, hlambda⟩ := hab.exists_nonneg_left ha
      refine ⟨-lambda, ?_, ?_⟩
      · simpa [neg_smul] using (congrArg Neg.neg hlambda).symm
      · intro mu hmu
        apply smul_left_injective ℝ ha
        exact hmu.symm.trans (by
          simpa [neg_smul] using (congrArg Neg.neg hlambda).symm)
  · rintro ⟨lambda, hlambda, _⟩
    rcases le_total 0 lambda with hlambda_nonneg | hlambda_nonpos
    · exact Or.inl (by
        rw [hlambda]
        exact SameRay.sameRay_nonneg_smul_right a hlambda_nonneg)
    · exact Or.inr (by
        rw [hlambda, ← neg_smul]
        exact SameRay.sameRay_nonneg_smul_right a (neg_nonneg.mpr hlambda_nonpos))

/-- Every vector parallel to a fixed nonzero direction has a unique scalar
coordinate along that direction. -/
theorem line_direction_unique_representation (a : PlaneVector) (ha : a ≠ 0) :
    ∀ b : PlaneVector, Parallel a b → ∃! lambda : ℝ, b = lambda • a := by
  intro b hab
  exact (parallel_iff_existsUnique_smul ha).mp hab

/-- Every real scalar multiple of a vector is parallel to that vector. -/
theorem scalar_multiple_parallel (lambda : ℝ) (a : PlaneVector) :
    Parallel a (lambda • a) := by
  rcases le_total 0 lambda with hlambda | hlambda
  · exact Or.inl (SameRay.sameRay_nonneg_smul_right a hlambda)
  · exact Or.inr (by
      rw [← neg_smul]
      exact SameRay.sameRay_nonneg_smul_right a (neg_nonneg.mpr hlambda))

/-- Parallel vectors whose moduli have ratio `mu` differ by the sign determined
by whether they point in the same or opposite direction. -/
theorem parallel_vector_representation {a b : PlaneVector} {mu : ℝ}
    (ha : a ≠ 0) (_hab : Parallel a b)
    (hnorm : vectorModulus b = mu * vectorModulus a) :
    (SameRay ℝ a b → b = mu • a) ∧
      (SameRay ℝ a (-b) → b = (-mu) • a) := by
  have ha_norm : 0 < vectorModulus a := by
    simpa [vectorModulus] using (norm_pos_iff.mpr ha)
  have hmu : 0 ≤ mu := by
    have hb_norm : 0 ≤ vectorModulus b := by
      exact norm_nonneg b
    nlinarith
  constructor
  · intro hab
    have hray : SameRay ℝ b (mu • a) :=
      hab.symm.trans (SameRay.sameRay_nonneg_smul_right a hmu)
        (fun h => (ha h).elim)
    apply hray.eq_of_norm_eq
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hmu]
    simpa [vectorModulus] using hnorm
  · intro hab
    have hray : SameRay ℝ (-b) (mu • a) :=
      hab.symm.trans (SameRay.sameRay_nonneg_smul_right a hmu)
        (fun h => (ha h).elim)
    have hneg : -b = mu • a := by
      apply hray.eq_of_norm_eq
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hmu]
      simpa [vectorModulus] using hnorm
    rw [← neg_inj]
    simpa using hneg

/-- The unoriented angle between two plane vectors. -/
noncomputable def vectorAngle (a b : PlaneVector) : ℝ :=
  InnerProductGeometry.angle a b

/-- Two plane vectors are perpendicular when their angle is `pi / 2`. -/
def Perpendicular (a b : PlaneVector) : Prop :=
  vectorAngle a b = Real.pi / 2

end HighSchoolMathLean.PlaneVectors
