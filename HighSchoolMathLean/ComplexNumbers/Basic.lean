/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace HighSchoolMathLean.ComplexNumbers

/-- The complex number with real part `a` and imaginary part `b`. -/
noncomputable def complexNumber (a b : ℝ) : ℂ :=
  ⟨a, b⟩

/-- The set of numbers obtained from arbitrary real and imaginary parts. -/
def complexSet : Set ℂ :=
  {z | ∃ a b : ℝ, z = complexNumber a b}

/-- The real part of a complex number. -/
def realPart (z : ℂ) : ℝ :=
  z.re

/-- The imaginary part of a complex number. -/
def imaginaryPart (z : ℂ) : ℝ :=
  z.im

/-- Two complex numbers given by real and imaginary coordinates are equal
exactly when both corresponding coordinates are equal. -/
theorem complexNumber_eq_iff (a b c d : ℝ) :
    complexNumber a b = complexNumber c d ↔ a = c ∧ b = d := by
  simp [complexNumber, Complex.ext_iff]

/-- A complex number is imaginary (non-real) when its imaginary part is
nonzero. -/
def IsImaginary (z : ℂ) : Prop :=
  imaginaryPart z ≠ 0

/-- A complex number is purely imaginary when its real part is zero and its
imaginary part is nonzero. -/
def IsPureImaginary (z : ℂ) : Prop :=
  realPart z = 0 ∧ imaginaryPart z ≠ 0

end HighSchoolMathLean.ComplexNumbers
