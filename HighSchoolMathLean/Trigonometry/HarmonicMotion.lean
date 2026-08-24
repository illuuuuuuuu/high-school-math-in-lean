/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Trigonometry.ProductAndSubstitutionIdentities
import Mathlib.Tactic

namespace HighSchoolMathLean.Trigonometry

/-- Translating every point of the sine graph left by `|phi|` when `phi ≥ 0`,
or right by `|phi|` when `phi < 0`, gives the graph of `sin (x + phi)`. -/
theorem sine_graph_phase_shift (phi x : ℝ) :
    (0 ≤ phi →
      sineFunction ((x - |phi|) + phi) = sineFunction x) ∧
    (phi < 0 →
      sineFunction ((x + |phi|) + phi) = sineFunction x) := by
  constructor
  · intro hphi
    rw [abs_of_nonneg hphi]
    ring_nf
  · intro hphi
    rw [abs_of_neg hphi]
    ring_nf

/-- For nonzero `omega`, horizontally scaling a sine-graph point's coordinate
by `1 / omega` places it on the graph of `sin (omega * x)`. -/
theorem sine_graph_horizontal_scale (omega x : ℝ) (homega : omega ≠ 0) :
    sineFunction (omega * (x / omega)) = sineFunction x := by
  congr 1
  field_simp

/-- Vertically scaling the sine graph by `A` gives the graph of
`x ↦ A * sin x`. -/
theorem sine_graph_vertical_scale (A x : ℝ) :
    (fun t : ℝ => A * sineFunction t) x = A * sineFunction x := by
  rfl

/-- A simple harmonic motion displacement on nonnegative time. -/
noncomputable def simpleHarmonicMotion (A omega phi : ℝ)
    (_hA : 0 < A) (_homega : 0 < omega) : Set.Ici (0 : ℝ) → ℝ :=
  fun x => A * sineFunction (omega * (x : ℝ) + phi)

/-- The amplitude parameter of a simple harmonic motion. -/
def harmonicAmplitude (A : ℝ) (_hA : 0 < A) : ℝ :=
  A

/-- The period associated with a positive angular frequency. -/
noncomputable def harmonicPeriod (omega : ℝ) (_homega : 0 < omega) : ℝ :=
  2 * Real.pi / omega

/-- Frequency is the reciprocal of the period and equals
`omega / (2 * pi)`. -/
theorem harmonicFrequency (omega : ℝ) (homega : 0 < omega) :
    1 / harmonicPeriod omega homega = omega / (2 * Real.pi) := by
  rw [harmonicPeriod]
  field_simp [ne_of_gt homega, Real.pi_ne_zero]

/-- The phase of a harmonic motion at time `x`. -/
def harmonicPhase (omega phi x : ℝ) : ℝ :=
  omega * x + phi

/-- At time zero, the phase is the initial phase `phi`. -/
theorem harmonicInitialPhase (omega phi : ℝ) :
    harmonicPhase omega phi 0 = phi := by
  simp [harmonicPhase]

end HighSchoolMathLean.Trigonometry
