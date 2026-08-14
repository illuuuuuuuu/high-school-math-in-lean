/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Set.Lattice

namespace HighSchoolMathLean.SetTheory

/-- Intersection of sets is associative. -/
theorem inter_associative {α : Type*} (A B C : Set α) :
    (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  constructor
  · rintro ⟨⟨hxA, hxB⟩, hxC⟩
    exact ⟨hxA, ⟨hxB, hxC⟩⟩
  · rintro ⟨hxA, ⟨hxB, hxC⟩⟩
    exact ⟨⟨hxA, hxB⟩, hxC⟩

/-- An intersection is contained in its left operand. -/
theorem inter_subset_left {α : Type*} (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.1

/-- An intersection is contained in its right operand. -/
theorem inter_subset_right {α : Type*} (A B : Set α) : A ∩ B ⊆ B := by
  intro x hx
  exact hx.2

/-- An intersection equals its left operand exactly when the left is contained in the right. -/
theorem inter_eq_left_iff_subset {α : Type*} (A B : Set α) :
    A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro hAB
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hxA
      exact ⟨hxA, hAB hxA⟩
  · intro hInter x hxA
    rw [← hInter] at hxA
    exact hxA.2

/-- An intersection equals its right operand exactly when the right is contained in the left. -/
theorem inter_eq_right_iff_subset {α : Type*} (A B : Set α) :
    B ⊆ A ↔ A ∩ B = B := by
  constructor
  · intro hBA
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hxB
      exact ⟨hBA hxB, hxB⟩
  · intro hInter x hxB
    rw [← hInter] at hxB
    exact hxB.1

/-- Union distributes over intersection. -/
theorem union_inter_distributive {α : Type*} (A B C : Set α) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (hxA | ⟨hxB, hxC⟩)
    · exact ⟨Or.inl hxA, Or.inl hxA⟩
    · exact ⟨Or.inr hxB, Or.inr hxC⟩
  · rintro ⟨hxAB, hxAC⟩
    rcases hxAB with hxA | hxB
    · exact Or.inl hxA
    · rcases hxAC with hxA | hxC
      · exact Or.inl hxA
      · exact Or.inr ⟨hxB, hxC⟩

/-- Intersection distributes over union. -/
theorem inter_union_distributive {α : Type*} (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · rintro ⟨hxA, hxB | hxC⟩
    · exact Or.inl ⟨hxA, hxB⟩
    · exact Or.inr ⟨hxA, hxC⟩
  · rintro (⟨hxA, hxB⟩ | ⟨hxA, hxC⟩)
    · exact ⟨hxA, Or.inl hxB⟩
    · exact ⟨hxA, Or.inr hxC⟩

/-- Taking the complement twice returns the original set. -/
theorem complement_complement {α : Type*} (A : Set α) : (Aᶜ)ᶜ = A := by
  classical
  ext x
  simp

/-- A set union its complement is the universal set. -/
theorem union_complement_univ {α : Type*} (A : Set α) : A ∪ Aᶜ = Set.univ := by
  classical
  ext x
  simp

/-- A complement union its original set is the universal set. -/
theorem complement_union_univ {α : Type*} (A : Set α) : Aᶜ ∪ A = Set.univ := by
  classical
  ext x
  simp

/-- A set and its complement have empty intersection. -/
theorem inter_complement_empty {α : Type*} (A : Set α) : A ∩ Aᶜ = ∅ := by
  ext x
  simp

/-- A complement and its original set have empty intersection. -/
theorem complement_inter_empty {α : Type*} (A : Set α) : Aᶜ ∩ A = ∅ := by
  ext x
  simp

end HighSchoolMathLean.SetTheory
