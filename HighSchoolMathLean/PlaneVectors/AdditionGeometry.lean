/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.PlaneVectors.Basic

namespace HighSchoolMathLean.PlaneVectors

/-- Vector addition is the additive operation of the Euclidean plane. -/
noncomputable def vectorAddition (a b : PlaneVector) : PlaneVector :=
  a + b

/-- Triangle rule: the vector from `A` to `B` plus the vector from `B` to `C`
is the vector from `A` to `C`. -/
theorem triangle_rule (A B C : PlaneVector) :
    vectorAddition (B - A) (C - B) = C - A := by
  simp [vectorAddition]

/-- Parallelogram rule: if `A - O` and `B - O` are adjacent sides, then the
diagonal from `O` to the fourth vertex `A + B - O` is their sum. -/
theorem parallelogram_rule (O A B : PlaneVector) :
    vectorAddition (A - O) (B - O) = (A + B - O) - O := by
  simp [vectorAddition]
  abel

end HighSchoolMathLean.PlaneVectors
