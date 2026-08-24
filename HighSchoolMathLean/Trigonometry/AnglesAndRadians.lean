/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Functions.LogarithmPropertiesAndAngles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace HighSchoolMathLean.Trigonometry

open HighSchoolMathLean.Functions

/-- A directed angle is positive when its signed rotation is counterclockwise. -/
def IsPositiveAngle (α : DirectedAngle) : Prop :=
  0 < α.rotation

/-- A directed angle is negative when its signed rotation is clockwise. -/
def IsNegativeAngle (α : DirectedAngle) : Prop :=
  α.rotation < 0

/-- A directed angle is zero when its ray has not rotated. -/
def IsZeroAngle (α : DirectedAngle) : Prop :=
  α.rotation = 0

/-- The radian measure of a central angle is arc length divided by radius. -/
def radianMeasure (arcLength radius : ℝ) : ℝ :=
  arcLength / radius

/-- For a nonzero radius, arc length is radian measure times radius. -/
theorem arcLength_eq_radianMeasure_mul_radius (arcLength radius : ℝ)
    (hradius : radius ≠ 0) :
    arcLength = radianMeasure arcLength radius * radius := by
  unfold radianMeasure
  field_simp

/-- The area of a sector with radian angle `α` and radius `r`. -/
def sectorArea (α r : ℝ) : ℝ :=
  (1 / 2 : ℝ) * α * r ^ 2

/-- Convert an angle measured in degrees to radians. -/
def degreesToRadians (θ : ℝ) : ℝ :=
  Real.pi / 180 * θ

/-- All real angles whose terminal side agrees with that of `α`. -/
def coterminalAngles (α : ℝ) : Set ℝ :=
  {β | ∃ k : ℤ, β = α + 2 * (k : ℝ) * Real.pi}

/-- The four open quadrant-angle sets. The `Fin 4` labels `0`, `1`, `2`, and
`3` represent the first, second, third, and fourth quadrants respectively. -/
def quadrantAngles : Set (Fin 4 × ℝ) :=
  {qα | ∃ k : ℤ,
    (qα.1 = (0 : Fin 4) ∧
      2 * (k : ℝ) * Real.pi < qα.2 ∧
      qα.2 < 2 * (k : ℝ) * Real.pi + Real.pi / 2) ∨
    (qα.1 = (1 : Fin 4) ∧
      2 * (k : ℝ) * Real.pi + Real.pi / 2 < qα.2 ∧
      qα.2 < 2 * (k : ℝ) * Real.pi + Real.pi) ∨
    (qα.1 = (2 : Fin 4) ∧
      2 * (k : ℝ) * Real.pi + Real.pi < qα.2 ∧
      qα.2 < 2 * (k : ℝ) * Real.pi + 3 * Real.pi / 2) ∨
    (qα.1 = (3 : Fin 4) ∧
      2 * (k : ℝ) * Real.pi + 3 * Real.pi / 2 < qα.2 ∧
      qα.2 < 2 * (k : ℝ) * Real.pi + 2 * Real.pi)}

/-- An axis angle is an integer multiple of `π / 2`. -/
def IsAxisAngle (α : ℝ) : Prop :=
  ∃ k : ℤ, α = (k : ℝ) * Real.pi / 2

end HighSchoolMathLean.Trigonometry
