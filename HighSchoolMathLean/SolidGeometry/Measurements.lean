/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.SolidGeometry.BasicSolids
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace HighSchoolMathLean.SolidGeometry

/-- The volume determined by the base area and height of a prism. -/
noncomputable def prismVolume (baseArea height : ℝ) : ℝ :=
  baseArea * height

/-- The volume determined by the base area and height of a pyramid. -/
noncomputable def pyramidVolume (baseArea height : ℝ) : ℝ :=
  (1 / 3 : ℝ) * baseArea * height

/-- The volume determined by the two base areas and height of a pyramidal
frustum. -/
noncomputable def pyramidFrustumVolume
    (upperBaseArea lowerBaseArea height : ℝ) : ℝ :=
  (1 / 3 : ℝ) * height *
    (upperBaseArea + Real.sqrt (upperBaseArea * lowerBaseArea) + lowerBaseArea)

/-- The total surface area determined by the radius and generator length of a
circular cylinder. -/
noncomputable def cylinderSurfaceArea (radius generatorLength : ℝ) : ℝ :=
  2 * Real.pi * radius * (radius + generatorLength)

/-- The total surface area determined by the radius and slant height of a
circular cone. -/
noncomputable def coneSurfaceArea (radius slantHeight : ℝ) : ℝ :=
  Real.pi * radius * (radius + slantHeight)

/-- The total surface area determined by the two radii and slant height of a
circular frustum. -/
noncomputable def circularFrustumSurfaceArea
    (upperRadius lowerRadius slantHeight : ℝ) : ℝ :=
  Real.pi *
    (upperRadius ^ 2 + lowerRadius ^ 2 +
      upperRadius * slantHeight + lowerRadius * slantHeight)

/-- The volume determined by the radius and height of a circular cylinder. -/
noncomputable def cylinderVolume (radius height : ℝ) : ℝ :=
  Real.pi * radius ^ 2 * height

/-- The volume determined by the radius and height of a circular cone. -/
noncomputable def coneVolume (radius height : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.pi * radius ^ 2 * height

/-- The volume determined by the two radii and height of a circular
frustum. -/
noncomputable def circularFrustumVolume
    (upperRadius lowerRadius height : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.pi * height *
    (upperRadius ^ 2 + upperRadius * lowerRadius + lowerRadius ^ 2)

/-- The surface area determined by the radius of a sphere. -/
noncomputable def sphereSurfaceArea (radius : ℝ) : ℝ :=
  4 * Real.pi * radius ^ 2

/-- The volume determined by the radius of a sphere. -/
noncomputable def sphereVolume (radius : ℝ) : ℝ :=
  (4 / 3 : ℝ) * Real.pi * radius ^ 3

/-- Zugeng's principle (Cavalieri's principle): bodies whose cross-sectional
area functions agree throughout the same height interval have equal volumes,
when volume is represented by the integral of cross-sectional area. -/
theorem zugeng_principle
    {lower upper : ℝ} {sectionArea₁ sectionArea₂ : ℝ → ℝ}
    {volume₁ volume₂ : ℝ}
    (hsections : Set.EqOn sectionArea₁ sectionArea₂ (Set.uIcc lower upper))
    (hvolume₁ : volume₁ = ∫ x in lower..upper, sectionArea₁ x)
    (hvolume₂ : volume₂ = ∫ x in lower..upper, sectionArea₂ x) :
    volume₁ = volume₂ := by
  rw [hvolume₁, hvolume₂]
  exact intervalIntegral.integral_congr hsections

/-- The unified volume formula for a prism or cylinder. -/
noncomputable def generalPrismVolume (baseArea height : ℝ) : ℝ :=
  baseArea * height

/-- The unified volume formula for a pyramid or cone. -/
noncomputable def generalPyramidVolume (baseArea height : ℝ) : ℝ :=
  (1 / 3 : ℝ) * baseArea * height

/-- The unified volume formula for a pyramidal or circular frustum. -/
noncomputable def generalFrustumVolume
    (upperBaseArea lowerBaseArea height : ℝ) : ℝ :=
  (1 / 3 : ℝ) * height *
    (upperBaseArea + Real.sqrt (upperBaseArea * lowerBaseArea) + lowerBaseArea)

end HighSchoolMathLean.SolidGeometry
