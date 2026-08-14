/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Functions.Rules

namespace HighSchoolMathLean.Functions

/-- Explicit and implicit expressions describing the same correspondence
impose equivalent conditions on every input-output pair. -/
theorem analytic_descriptions_equivalent (R : Correspondence ℝ ℝ)
    (g : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (hg : IsExplicitExpression R g) (hF : IsImplicitExpression R F) :
    ∀ x y, y = g x ↔ F x y = 0 := by
  intro x y
  exact (hg x y).symm.trans (hF.1 x y)

/-- An analytic formula packages either an explicit expression or an implicit
equation together with the fact that it describes the correspondence. -/
inductive AnalyticFormula (R : Correspondence ℝ ℝ) where
  | explicit (g : ℝ → ℝ) (describes : IsExplicitExpression R g)
  | implicit (F : ℝ → ℝ → ℝ) (describes : IsImplicitExpression R F)

/-- Analytic descriptions are exact: related pairs satisfy the corresponding
explicit equality or implicit equation without approximation. -/
theorem analytic_method_exact (R : Correspondence ℝ ℝ) :
    (∀ g : ℝ → ℝ, IsExplicitExpression R g →
      ∀ x y, R x y → y = g x) ∧
    (∀ F : ℝ → ℝ → ℝ, IsImplicitExpression R F →
      ∀ x y, R x y → F x y = 0) := by
  constructor
  · intro g hg x y hxy
    exact (hg x y).mp hxy
  · intro F hF x y hxy
    exact (hF.1 x y).mp hxy

/-- A set of ordered pairs is a listing of a correspondence when it contains
exactly all related input-output pairs. -/
def IsListingMethod (R : Correspondence ℝ ℝ) (L : Set (ℝ × ℝ)) : Prop :=
  ∀ x y, (x, y) ∈ L ↔ R x y

/-- A set of coordinate points graphs a correspondence when membership of
`(x, y)` is equivalent to the correspondence relating `x` and `y`. -/
def IsGraphingMethod (R : Correspondence ℝ ℝ) (G : Set (ℝ × ℝ)) : Prop :=
  ∀ x y, (x, y) ∈ G ↔ R x y

/-- A real function is strictly increasing on `I`, which lies in its domain
`D`, when order of inputs in `I` is strictly preserved. -/
def IsStrictlyIncreasingOn (f : ℝ → ℝ) (D I : Set ℝ) : Prop :=
  I ⊆ D ∧ StrictMonoOn f I

/-- A real function is strictly decreasing on `I`, which lies in its domain
`D`, when order of inputs in `I` is strictly reversed. -/
def IsStrictlyDecreasingOn (f : ℝ → ℝ) (D I : Set ℝ) : Prop :=
  I ⊆ D ∧ StrictAntiOn f I

/-- An interval is a strict monotonicity interval when the function is either
strictly increasing or strictly decreasing there. -/
def IsStrictMonotonicInterval (f : ℝ → ℝ) (D I : Set ℝ) : Prop :=
  IsStrictlyIncreasingOn f D I ∨ IsStrictlyDecreasingOn f D I

/-- `M` is the maximum value of `f` on `D` when it bounds every value above
and is attained at some point of `D`. -/
def IsMaximumValue (f : ℝ → ℝ) (D : Set ℝ) (M : ℝ) : Prop :=
  (∀ x ∈ D, f x ≤ M) ∧ ∃ x₀ ∈ D, f x₀ = M

/-- `m` is the minimum value of `f` on `D` when it bounds every value below
and is attained at some point of `D`. -/
def IsMinimumValue (f : ℝ → ℝ) (D : Set ℝ) (m : ℝ) : Prop :=
  (∀ x ∈ D, m ≤ f x) ∧ ∃ x₀ ∈ D, f x₀ = m

end HighSchoolMathLean.Functions
