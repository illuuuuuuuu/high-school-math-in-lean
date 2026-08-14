/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Set.Lattice

namespace HighSchoolMathLean.Logic

/-- Logical equivalence is symmetric. -/
theorem iff_commutative {p q : Prop} (h : p ↔ q) : q ↔ p := by
  constructor
  · exact h.mpr
  · exact h.mp

/-- The negation of a restricted universal statement yields a counterexample. -/
theorem not_forall_mem_iff_exists_mem_not {α : Type*} (M : Set α) (p : α → Prop) :
    (¬ ∀ x ∈ M, p x) ↔ ∃ x ∈ M, ¬ p x := by
  classical
  constructor
  · intro hNotAll
    by_contra hNoCounterexample
    apply hNotAll
    intro x hxM
    by_contra hNotP
    exact hNoCounterexample ⟨x, hxM, hNotP⟩
  · rintro ⟨x, hxM, hNotP⟩ hAll
    exact hNotP (hAll x hxM)

/-- A restricted existential statement is false exactly when every candidate fails. -/
theorem not_exists_mem_iff_forall_mem_not {α : Type*} (M : Set α) (p : α → Prop) :
    (¬ ∃ x ∈ M, p x) ↔ ∀ x ∈ M, ¬ p x := by
  constructor
  · intro hNotExists x hxM hxP
    exact hNotExists ⟨x, hxM, hxP⟩
  · intro hAll
    rintro ⟨x, hxM, hxP⟩
    exact hAll x hxM hxP

end HighSchoolMathLean.Logic
