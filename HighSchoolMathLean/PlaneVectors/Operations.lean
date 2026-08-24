/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.PlaneVectors.AdditionGeometry

namespace HighSchoolMathLean.PlaneVectors

/-- Adding the zero vector on either side leaves a vector unchanged. -/
theorem zero_addition_rule (a : PlaneVector) :
    vectorAddition a 0 = a ∧ vectorAddition 0 a = a := by
  simp [vectorAddition]

/-- The triangle inequality for vector addition, together with its equality
condition: equality holds exactly for vectors on the same ray. -/
theorem triangle_inequality_for_addition (a b : PlaneVector) :
    vectorModulus (vectorAddition a b) ≤ vectorModulus a + vectorModulus b ∧
      (vectorModulus (vectorAddition a b) = vectorModulus a + vectorModulus b ↔
        SameRay ℝ a b) := by
  constructor
  · exact norm_add_le a b
  · exact sameRay_iff_norm_add.symm

/-- Vector addition is commutative. -/
theorem vector_addition_commutative (a b : PlaneVector) :
    vectorAddition a b = vectorAddition b a := by
  simp [vectorAddition, add_comm]

/-- Vector addition is associative. -/
theorem vector_addition_associative (a b c : PlaneVector) :
    vectorAddition (vectorAddition a b) c =
      vectorAddition a (vectorAddition b c) := by
  simp [vectorAddition, add_assoc]

/-- The opposite vector of `a` is its additive inverse. -/
noncomputable def oppositeVector (a : PlaneVector) : PlaneVector :=
  -a

/-- The opposite of the zero vector is the zero vector. -/
theorem opposite_zero : oppositeVector 0 = (0 : PlaneVector) := by
  simp [oppositeVector]

/-- A vector plus its opposite is zero in either order. -/
theorem add_opposite_rule (a : PlaneVector) :
    vectorAddition a (oppositeVector a) = 0 ∧
      vectorAddition (oppositeVector a) a = 0 := by
  simp [vectorAddition, oppositeVector]

/-- Vector subtraction is addition of the opposite vector. -/
noncomputable def vectorSubtraction (a b : PlaneVector) : PlaneVector :=
  vectorAddition a (oppositeVector b)

/-- If two vectors have common origin `O`, their difference points from the
endpoint of the second vector to the endpoint of the first. -/
theorem subtraction_geometric_meaning (O A B : PlaneVector) :
    vectorSubtraction (A - O) (B - O) = A - B := by
  simp [vectorSubtraction, vectorAddition, oppositeVector]

/-- Scalar multiplication scales the modulus by `|lambda|`; positive scalars
preserve direction and negative scalars reverse it. -/
theorem scalar_multiplication_rules (lambda : ℝ) (a : PlaneVector) :
    vectorModulus (lambda • a) = |lambda| * vectorModulus a ∧
      (0 < lambda → SameRay ℝ (lambda • a) a) ∧
      (lambda < 0 → SameRay ℝ (lambda • a) (-a)) := by
  constructor
  · simp [vectorModulus, norm_smul, Real.norm_eq_abs]
  · constructor
    · intro hlambda
      exact SameRay.sameRay_pos_smul_left a hlambda
    · intro hlambda
      exact sameRay_neg_smul_left_iff.mpr (Or.inl hlambda.le)

end HighSchoolMathLean.PlaneVectors
