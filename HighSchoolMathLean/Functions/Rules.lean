/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Basic

namespace HighSchoolMathLean.Functions

/-- A real-valued explicit rule assigns the output by evaluating a real function. -/
def IsExplicitRule (f : ℝ → ℝ) (x y : ℝ) : Prop :=
  y = f x

/-- An implicit real rule relates an input and an output through an equation. -/
def IsImplicitRule (F : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  F x y = 0

/-- A correspondence is a binary relation between possible inputs and outputs. -/
abbrev Correspondence (α β : Type*) := α → β → Prop

/-- A correspondence is functional from `A` to `B` when every input in `A`
has exactly one related output in `B`. -/
def IsFunctionOn {α β : Type*} (R : Correspondence α β)
    (A : Set α) (B : Set β) : Prop :=
  ∀ x ∈ A, ∃! y, y ∈ B ∧ R x y

/-- An independent value is an admitted input that is related to an output. -/
def IsIndependentVariable {α β : Type*} (R : Correspondence α β)
    (A : Set α) (x : α) : Prop :=
  x ∈ A ∧ ∃ y, R x y

/-- A dependent value is an admitted output produced by some input. -/
def IsDependentVariable {α β : Type*} (R : Correspondence α β)
    (B : Set β) (y : β) : Prop :=
  y ∈ B ∧ ∃ x, R x y

/-- `A` is precisely the domain of a correspondence when its members are
exactly the inputs related to at least one output. -/
def IsDomain {α β : Type*} (R : Correspondence α β) (A : Set α) : Prop :=
  ∀ x, x ∈ A ↔ ∃ y, R x y

/-- `B` is precisely the range of a correspondence when its members are
exactly the outputs related to at least one input. -/
def IsRange {α β : Type*} (R : Correspondence α β) (B : Set β) : Prop :=
  ∀ y, y ∈ B ↔ ∃ x, R x y

/-- A function `g` explicitly describes a real correspondence when the
correspondence holds exactly when `y = g x`. -/
def IsExplicitExpression (R : Correspondence ℝ ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x y, R x y ↔ y = g x

/-- An equation implicitly describes a real functional correspondence when
its zero set is the correspondence and determines a unique output per input. -/
def IsImplicitExpression (R : Correspondence ℝ ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, R x y ↔ F x y = 0) ∧ ∀ x, ∃! y, F x y = 0

/-- A real correspondence has an analytic description when it has either an
explicit expression or an implicit equation. -/
def HasAnalyticMethod (R : Correspondence ℝ ℝ) : Prop :=
  (∃ g : ℝ → ℝ, IsExplicitExpression R g) ∨
    ∃ F : ℝ → ℝ → ℝ, IsImplicitExpression R F

end HighSchoolMathLean.Functions
