/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

namespace HighSchoolMathLean.PlaneVectors

/-- A plane vector is represented by a vector in the real Euclidean plane. -/
abbrev PlaneVector := EuclideanSpace ℝ (Fin 2)

/-- The modulus of a plane vector is its Euclidean norm. -/
noncomputable def vectorModulus (a : PlaneVector) : ℝ :=
  ‖a‖

/-- A plane vector is zero exactly when its modulus is zero. -/
theorem eq_zero_iff_vectorModulus_eq_zero (a : PlaneVector) :
    a = 0 ↔ vectorModulus a = 0 := by
  simp [vectorModulus]

/-- Two plane vectors are parallel when they have the same or opposite direction.
This definition also regards the zero vector as parallel to every vector. -/
def Parallel (a b : PlaneVector) : Prop :=
  SameRay ℝ a b ∨ SameRay ℝ a (-b)

/-- The zero vector is parallel to every plane vector. -/
theorem zero_parallel (a : PlaneVector) : Parallel 0 a := by
  exact Or.inl (SameRay.zero_left a)

/-- Two plane vectors are equal exactly when they have the same direction and
the same modulus. -/
theorem eq_iff_sameRay_and_vectorModulus_eq (a b : PlaneVector) :
    a = b ↔ SameRay ℝ a b ∧ vectorModulus a = vectorModulus b := by
  constructor
  · intro h
    subst b
    exact ⟨SameRay.rfl, rfl⟩
  · rintro ⟨hab, hnorm⟩
    exact hab.eq_of_norm_eq hnorm

/-- Parallelism is transitive when the middle vector is nonzero. -/
theorem parallel_trans {a b c : PlaneVector}
    (hab : Parallel a b) (hbc : Parallel b c) (hb : b ≠ 0) :
    Parallel a c := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact Or.inl (hab.trans hbc (fun h => (hb h).elim))
  · exact Or.inr (hab.trans hbc (fun h => (hb h).elim))
  · exact Or.inr (hab.trans hbc.neg (fun h => (hb (neg_eq_zero.mp h)).elim))
  · exact Or.inl (hab.trans (by simpa using hbc.neg)
      (fun h => (hb (neg_eq_zero.mp h)).elim))

end HighSchoolMathLean.PlaneVectors
