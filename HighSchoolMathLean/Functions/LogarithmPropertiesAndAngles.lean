/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Functions.ExponentialAndLogarithm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace HighSchoolMathLean.Functions

/-- Product, quotient, and real-power laws for logarithms. In the third law,
the same positive number `M` occurs on both sides. -/
theorem logarithm_operation_properties (a M N n : ℝ)
    (_ha : 0 < a) (_hane : a ≠ 1) (hM : 0 < M) (hN : 0 < N) :
    Real.logb a (M * N) = Real.logb a M + Real.logb a N ∧
    Real.logb a (M / N) = Real.logb a M - Real.logb a N ∧
    Real.logb a (Real.rpow M n) = n * Real.logb a M := by
  exact ⟨Real.logb_mul hM.ne' hN.ne',
    Real.logb_div hM.ne' hN.ne',
    Real.logb_rpow_eq_mul_logb_of_pos hM⟩

/-- Changing from one valid logarithm base to another preserves the value. -/
theorem logarithm_change_of_base (a b c : ℝ)
    (ha : 0 < a) (hane : a ≠ 1) (_hb : 0 < b)
    (hc : 0 < c) (hcne : c ≠ 1) :
    Real.logb a b = Real.logb c b / Real.logb c a := by
  have hla : Real.log a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ha hane
  have hlc : Real.log c ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hc hcne
  unfold Real.logb
  field_simp [hla, hlc, div_ne_zero hla hlc]

/-- A logarithm function has a valid base and agrees with `Real.logb` on the
positive real numbers, its mathematical domain. -/
def IsLogarithmFunction (f : ℝ → ℝ) (a : ℝ) : Prop :=
  0 < a ∧ a ≠ 1 ∧ ∀ x ∈ Set.Ioi (0 : ℝ), f x = Real.logb a x

/-- Replacing a logarithm base by its reciprocal reflects every value across
the horizontal axis. -/
theorem logarithm_reciprocal_base_symmetry (a x : ℝ) :
    Real.logb a⁻¹ x = -Real.logb a x := by
  exact Real.logb_inv_base a x

/-- On every positive input, a logarithm function is given by its logarithmic
formula; hence its graph lies strictly to the right of the vertical axis. -/
theorem logarithmFunction_domain {f : ℝ → ℝ} {a x : ℝ}
    (hf : IsLogarithmFunction f a) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    f x = Real.logb a x :=
  hf.2.2 x hx

/-- The image of the positive domain of a logarithm function is all reals. -/
theorem logarithmFunction_range {f : ℝ → ℝ} {a : ℝ}
    (hf : IsLogarithmFunction f a) :
    f '' Set.Ioi (0 : ℝ) = Set.univ := by
  rcases hf with ⟨ha, hane, hf⟩
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    rcases Real.surjOn_logb ha hane (Set.mem_univ y) with ⟨x, hx, hxy⟩
    refine ⟨x, hx, ?_⟩
    rw [hf x hx]
    exact hxy

/-- Every logarithm function passes through `(1, 0)`. -/
theorem logarithmFunction_one {f : ℝ → ℝ} {a : ℝ}
    (hf : IsLogarithmFunction f a) :
    f 1 = 0 := by
  have h_one_pos : (1 : ℝ) ∈ Set.Ioi 0 := by
    exact Set.mem_Ioi.mpr zero_lt_one
  rw [hf.2.2 1 h_one_pos]
  simp [Real.logb]

/-- Logarithm functions increase for bases greater than one and decrease for
bases between zero and one. -/
theorem logarithmFunction_monotonicity {f : ℝ → ℝ} {a : ℝ}
    (hf : IsLogarithmFunction f a) :
    (1 < a → StrictMonoOn f (Set.Ioi (0 : ℝ))) ∧
    (0 < a ∧ a < 1 → StrictAntiOn f (Set.Ioi (0 : ℝ))) := by
  constructor
  · intro ha x hx y hy hxy
    rw [hf.2.2 x hx, hf.2.2 y hy]
    exact Real.strictMonoOn_logb ha hx hy hxy
  · rintro ⟨ha, halt⟩ x hx y hy hxy
    rw [hf.2.2 x hx, hf.2.2 y hy]
    exact Real.strictAntiOn_logb_of_base_lt_one ha halt hx hy hxy

/-- Exponentiation and logarithm to the same valid base undo one another on
their respective domains. -/
theorem exponential_logarithm_inverse (a : ℝ) (ha : 0 < a) (hane : a ≠ 1) :
    (∀ x : ℝ, Real.logb a (Real.rpow a x) = x) ∧
    (∀ y : ℝ, 0 < y → Real.rpow a (Real.logb a y) = y) := by
  constructor
  · intro x
    exact Real.logb_rpow ha hane
  · intro y hy
    exact Real.rpow_logb ha hane hy

/-- A directed angle records a vertex, an initial ray direction, a signed
rotation, and the terminal ray obtained by the planar rotation formula. -/
structure DirectedAngle where
  vertex : ℝ × ℝ
  initialDirection : ℝ × ℝ
  initialDirection_ne_zero : initialDirection ≠ (0, 0)
  rotation : ℝ
  terminalDirection : ℝ × ℝ
  terminal_eq_rotation :
    terminalDirection =
      (Real.cos rotation * initialDirection.1 - Real.sin rotation * initialDirection.2,
       Real.sin rotation * initialDirection.1 + Real.cos rotation * initialDirection.2)

end HighSchoolMathLean.Functions
