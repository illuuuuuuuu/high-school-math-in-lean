/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Set.Lattice

namespace HighSchoolMathLean.SetTheory

/-- Relative complement distributes over union. -/
theorem diff_union_distrib {α : Type*} (U A B : Set α) :
    U \ (A ∪ B) = (U \ A) ∩ (U \ B) := by
  ext x
  simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff]
  constructor
  · rintro ⟨hxU, hxAB⟩
    exact
      ⟨⟨hxU, fun hxA => hxAB (Or.inl hxA)⟩,
       ⟨hxU, fun hxB => hxAB (Or.inr hxB)⟩⟩
  · rintro ⟨⟨hxU, hxA⟩, ⟨_, hxB⟩⟩
    refine ⟨hxU, ?_⟩
    rintro (hxA' | hxB')
    · exact hxA hxA'
    · exact hxB hxB'

/-- Relative complement transforms intersection into union. -/
theorem diff_inter_distrib {α : Type*} (U A B : Set α) :
    U \ (A ∩ B) = (U \ A) ∪ (U \ B) := by
  classical
  ext x
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨hxU, hxAB⟩
    by_cases hxA : x ∈ A
    · exact Or.inr ⟨hxU, fun hxB => hxAB ⟨hxA, hxB⟩⟩
    · exact Or.inl ⟨hxU, hxA⟩
  · rintro (⟨hxU, hxA⟩ | ⟨hxU, hxB⟩)
    · exact ⟨hxU, fun hxAB => hxA hxAB.1⟩
    · exact ⟨hxU, fun hxAB => hxB hxAB.2⟩

end HighSchoolMathLean.SetTheory
