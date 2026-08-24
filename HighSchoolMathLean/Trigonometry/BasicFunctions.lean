/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Trigonometry.AnglesAndRadians
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace HighSchoolMathLean.Trigonometry

/-- The real sine function. -/
noncomputable def sineFunction : ℝ → ℝ :=
  Real.sin

/-- The real cosine function. -/
noncomputable def cosineFunction : ℝ → ℝ :=
  Real.cos

/-- The real tangent function. -/
noncomputable def tangentFunction : ℝ → ℝ :=
  Real.tan

/-- The Pythagorean identity for sine and cosine. -/
theorem sine_sq_add_cosine_sq (α : ℝ) :
    sineFunction α ^ 2 + cosineFunction α ^ 2 = 1 := by
  change Real.sin α ^ 2 + Real.cos α ^ 2 = 1
  exact Real.sin_sq_add_cos_sq α

/-- Where cosine is nonzero, tangent is sine divided by cosine. -/
theorem sine_div_cosine_eq_tangent (α : ℝ)
    (_hcos : cosineFunction α ≠ 0) :
    sineFunction α / cosineFunction α = tangentFunction α := by
  simpa [sineFunction, cosineFunction, tangentFunction] using
    (Real.tan_eq_sin_div_cos α).symm

/-- Sine and cosine are unchanged after adding or subtracting one full turn. -/
theorem sine_cosine_two_pi_periodicity (x : ℝ) :
    (sineFunction (x + 2 * Real.pi) = sineFunction x ∧
      sineFunction (x - 2 * Real.pi) = sineFunction x) ∧
    (cosineFunction (x + 2 * Real.pi) = cosineFunction x ∧
      cosineFunction (x - 2 * Real.pi) = cosineFunction x) := by
  simp [sineFunction, cosineFunction]

/-- The sine curve is continuous and smooth to every order. -/
theorem sineCurve_continuous_and_smooth :
    Continuous sineFunction ∧ ContDiff ℝ ⊤ sineFunction := by
  exact ⟨Real.continuous_sin, Real.contDiff_sin⟩

/-- The cosine curve is a left shift of the sine curve by `π / 2`; it is also
continuous and smooth to every order. -/
theorem cosineCurve_shift_continuous_and_smooth :
    (∀ x : ℝ, cosineFunction x = sineFunction (x + Real.pi / 2)) ∧
    Continuous cosineFunction ∧ ContDiff ℝ ⊤ cosineFunction := by
  refine ⟨?_, Real.continuous_cos, Real.contDiff_cos⟩
  intro x
  simpa [sineFunction, cosineFunction] using (Real.sin_add_pi_div_two x).symm

/-- Every integer multiple of `2π` is a sine period, and `2π` is the least
positive period. -/
theorem sine_periods_and_least_positive_period :
    (∀ k : ℤ, Function.Periodic sineFunction ((k : ℝ) * (2 * Real.pi))) ∧
    (0 < 2 * Real.pi ∧ Function.Periodic sineFunction (2 * Real.pi) ∧
      ∀ T : ℝ, 0 < T → Function.Periodic sineFunction T → 2 * Real.pi ≤ T) := by
  constructor
  · intro k x
    exact Real.sin_add_int_mul_two_pi x k
  · refine ⟨by positivity, Real.sin_periodic, ?_⟩
    intro T hT hperiod
    change Function.Periodic Real.sin T at hperiod
    have hcos : Real.cos T = 1 := by
      have hshift := hperiod (Real.pi / 2)
      simpa [Real.sin_add] using hshift
    rcases (Real.cos_eq_one_iff T).mp hcos with ⟨k, hk⟩
    have hkpos_real : (0 : ℝ) < (k : ℝ) := by
      nlinarith [Real.pi_pos]
    have hkpos : (0 : ℤ) < k := by
      exact_mod_cast hkpos_real
    have hkone : (1 : ℤ) ≤ k := by
      omega
    have hkone_real : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hkone
    nlinarith [Real.pi_pos]

/-- Every integer multiple of `2π` is a cosine period, and `2π` is the least
positive period. -/
theorem cosine_periods_and_least_positive_period :
    (∀ k : ℤ, Function.Periodic cosineFunction ((k : ℝ) * (2 * Real.pi))) ∧
    (0 < 2 * Real.pi ∧ Function.Periodic cosineFunction (2 * Real.pi) ∧
      ∀ T : ℝ, 0 < T → Function.Periodic cosineFunction T → 2 * Real.pi ≤ T) := by
  constructor
  · intro k x
    exact Real.cos_add_int_mul_two_pi x k
  · refine ⟨by positivity, Real.cos_periodic, ?_⟩
    intro T hT hperiod
    change Function.Periodic Real.cos T at hperiod
    have hcos : Real.cos T = 1 := by
      have hzero := hperiod 0
      simpa using hzero
    rcases (Real.cos_eq_one_iff T).mp hcos with ⟨k, hk⟩
    have hkpos_real : (0 : ℝ) < (k : ℝ) := by
      nlinarith [Real.pi_pos]
    have hkpos : (0 : ℤ) < k := by
      exact_mod_cast hkpos_real
    have hkone : (1 : ℤ) ≤ k := by
      omega
    have hkone_real : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hkone
    nlinarith [Real.pi_pos]

end HighSchoolMathLean.Trigonometry
