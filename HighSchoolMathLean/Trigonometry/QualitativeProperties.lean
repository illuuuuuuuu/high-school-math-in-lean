/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Trigonometry.BasicFunctions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

namespace HighSchoolMathLean.Trigonometry

/-- The sine function is odd. -/
theorem sineFunction_odd (x : ℝ) :
    sineFunction (-x) = -sineFunction x := by
  simp [sineFunction]

/-- The cosine function is even. -/
theorem cosineFunction_even (x : ℝ) :
    cosineFunction (-x) = cosineFunction x := by
  simp [cosineFunction]

/-- On every full-turn translate, sine increases from `-π/2` to `π/2` and
decreases from `π/2` to `3π/2`. The intervals are parametrized from the
standard intervals to make the translation explicit. -/
theorem sineFunction_monotonicity (k : ℤ) :
    StrictMonoOn
      (fun x => sineFunction (x + (k : ℝ) * (2 * Real.pi)))
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    StrictAntiOn
      (fun x => sineFunction ((x + Real.pi / 2) + (k : ℝ) * (2 * Real.pi)))
      (Set.Icc 0 Real.pi) := by
  constructor
  · intro x hx y hy hxy
    simpa [sineFunction] using Real.strictMonoOn_sin hx hy hxy
  · intro x hx y hy hxy
    have hcos := Real.strictAntiOn_cos hx hy hxy
    calc
      sineFunction ((y + Real.pi / 2) + (k : ℝ) * (2 * Real.pi)) =
          Real.cos y := by
        rw [sineFunction, Real.sin_add_int_mul_two_pi,
          Real.sin_add_pi_div_two]
      _ < Real.cos x := hcos
      _ = sineFunction ((x + Real.pi / 2) + (k : ℝ) * (2 * Real.pi)) := by
        rw [sineFunction, Real.sin_add_int_mul_two_pi,
          Real.sin_add_pi_div_two]

/-- Corrected cosine monotonicity: cosine decreases from `2kπ` to
`π + 2kπ` and increases from `π + 2kπ` to `2π + 2kπ`. -/
theorem cosineFunction_monotonicity (k : ℤ) :
    StrictAntiOn
      (fun x => cosineFunction (x + (k : ℝ) * (2 * Real.pi)))
      (Set.Icc 0 Real.pi) ∧
    StrictMonoOn
      (fun x => cosineFunction ((x + Real.pi) + (k : ℝ) * (2 * Real.pi)))
      (Set.Icc 0 Real.pi) := by
  constructor
  · intro x hx y hy hxy
    simpa [cosineFunction] using Real.strictAntiOn_cos hx hy hxy
  · intro x hx y hy hxy
    have hcos := Real.strictAntiOn_cos hx hy hxy
    simpa [cosineFunction] using (neg_lt_neg hcos)

/-- Sine equals `1` exactly at `π/2 + 2kπ`, and equals `-1` exactly at
`3π/2 + 2kπ`. -/
theorem sineFunction_extrema (x : ℝ) :
    (sineFunction x = 1 ↔
      ∃ k : ℤ, Real.pi / 2 + (k : ℝ) * (2 * Real.pi) = x) ∧
    (sineFunction x = -1 ↔
      ∃ k : ℤ, 3 * Real.pi / 2 + (k : ℝ) * (2 * Real.pi) = x) := by
  constructor
  · simpa [sineFunction] using (Real.sin_eq_one_iff (x := x))
  · rw [sineFunction, Real.sin_eq_neg_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      rw [← hk]
      push_cast
      ring
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [← hk]
      push_cast
      ring

/-- Corrected cosine extrema: cosine equals `1` exactly at `2kπ`, and equals
`-1` exactly at `π + 2kπ`. -/
theorem cosineFunction_extrema (x : ℝ) :
    (cosineFunction x = 1 ↔
      ∃ k : ℤ, (k : ℝ) * (2 * Real.pi) = x) ∧
    (cosineFunction x = -1 ↔
      ∃ k : ℤ, Real.pi + (k : ℝ) * (2 * Real.pi) = x) := by
  exact ⟨by simpa [cosineFunction] using (Real.cos_eq_one_iff x),
    by simpa [cosineFunction] using (Real.cos_eq_neg_one_iff (x := x))⟩

/-- The tangent function has period `π`. -/
theorem tangentFunction_periodic :
    Function.Periodic tangentFunction Real.pi := by
  exact Real.tan_periodic

/-- The tangent function is odd. -/
theorem tangentFunction_odd (x : ℝ) :
    tangentFunction (-x) = -tangentFunction x := by
  simp [tangentFunction]

/-- The vertical asymptotes separating the branches of the tangent curve. -/
noncomputable def tangentAsymptotes : Set ℝ :=
  {x | ∃ k : ℤ, x = Real.pi / 2 + (k : ℝ) * Real.pi}

/-- Tangent is strictly increasing on every interval between consecutive
vertical asymptotes. -/
theorem tangentFunction_strictMonoOn_branch (k : ℤ) :
    StrictMonoOn tangentFunction
      (Set.Ioo (-(Real.pi / 2) + (k : ℝ) * Real.pi)
        (Real.pi / 2 + (k : ℝ) * Real.pi)) := by
  intro x hx y hy hxy
  have hx' : x - (k : ℝ) * Real.pi ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : y - (k : ℝ) * Real.pi ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hy.1, hy.2]
  have htan := Real.strictMonoOn_tan hx' hy' (sub_lt_sub_right hxy _)
  change Real.tan x < Real.tan y
  calc
    Real.tan x = Real.tan (x - (k : ℝ) * Real.pi) :=
      (Real.tan_sub_int_mul_pi x k).symm
    _ < Real.tan (y - (k : ℝ) * Real.pi) := htan
    _ = Real.tan y := Real.tan_sub_int_mul_pi y k

end HighSchoolMathLean.Trigonometry
