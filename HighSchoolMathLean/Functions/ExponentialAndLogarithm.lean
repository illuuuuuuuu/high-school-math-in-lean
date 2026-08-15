/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Functions.FractionalPowers
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace HighSchoolMathLean.Functions

/-- A real exponential function has a positive base different from one and
maps each real exponent to the corresponding real power. -/
def IsExponentialFunction (f : ℝ → ℝ) (a : ℝ) : Prop :=
  0 < a ∧ a ≠ 1 ∧ ∀ x : ℝ, f x = Real.rpow a x

/-- Every real exponential function passes through `(0, 1)`. -/
theorem exponentialFunction_zero {f : ℝ → ℝ} {a : ℝ}
    (hf : IsExponentialFunction f a) :
    f 0 = 1 := by
  rw [hf.2.2 0]
  exact Real.rpow_zero a

/-- The range of a real exponential function is exactly the positive reals. -/
theorem exponentialFunction_range {f : ℝ → ℝ} {a : ℝ}
    (hf : IsExponentialFunction f a) :
    Set.range f = Set.Ioi 0 := by
  rcases hf with ⟨ha, hane, hf⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [hf x]
    exact Real.rpow_pos_of_pos ha x
  · intro hy
    refine ⟨Real.logb a y, ?_⟩
    rw [hf]
    exact Real.rpow_logb ha hane hy

/-- Exponential functions decrease for bases between zero and one and
increase for bases greater than one. -/
theorem exponentialFunction_monotonicity {f : ℝ → ℝ} {a : ℝ}
    (hf : IsExponentialFunction f a) :
    (0 < a ∧ a < 1 → StrictAnti f) ∧
    (1 < a → StrictMono f) := by
  constructor
  · rintro ⟨ha, halt⟩ x y hxy
    rw [hf.2.2 x, hf.2.2 y]
    exact Real.strictAnti_rpow_of_base_lt_one ha halt hxy
  · intro hagt x y hxy
    rw [hf.2.2 x, hf.2.2 y]
    exact Real.strictMono_rpow_of_base_gt_one hagt hxy

/-- `x` is a logarithm of the positive number `N` to base `a` exactly when
raising `a` to `x` gives `N`. -/
def IsLogarithm (a N x : ℝ) : Prop :=
  Real.rpow a x = N

/-- A common logarithm is a logarithm to base ten. -/
def IsCommonLogarithm (N x : ℝ) : Prop :=
  IsLogarithm 10 N x

/-- A natural logarithm is the exponent whose real exponential is `N`. -/
def IsNaturalLogarithm (N x : ℝ) : Prop :=
  Real.exp x = N

/-- For a valid base and positive argument, the logarithmic and exponential
forms are equivalent. -/
theorem logarithm_exponential_relation {a N x : ℝ}
    (ha : 0 < a) (hane : a ≠ 1) (hN : 0 < N) :
    IsLogarithm a N x ↔ x = Real.logb a N := by
  constructor
  · intro h
    exact ((Real.logb_eq_iff_rpow_eq ha hane hN).2 h).symm
  · intro h
    exact (Real.logb_eq_iff_rpow_eq ha hane hN).1 h.symm

/-- A nonpositive real number has no real logarithm to a positive base. -/
theorem no_logarithm_of_nonpositive {a N x : ℝ}
    (ha : 0 < a) (hN : N ≤ 0) :
    ¬ IsLogarithm a N x := by
  intro h
  have hrpow : 0 < Real.rpow a x := Real.rpow_pos_of_pos ha x
  change Real.rpow a x = N at h
  linarith

/-- The logarithm of the base is one, and the logarithm of one is zero. -/
theorem logarithm_basic_properties (a : ℝ) (_ha : 0 < a) (_hane : a ≠ 1) :
    IsLogarithm a a 1 ∧ IsLogarithm a 1 0 := by
  constructor
  · simp [IsLogarithm]
  · simp [IsLogarithm]

end HighSchoolMathLean.Functions
