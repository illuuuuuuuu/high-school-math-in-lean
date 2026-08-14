/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Set.Lattice

namespace HighSchoolMathLean.SetTheory

/-- Every set is a subset of itself. -/
theorem subset_reflexive {α : Type*} (A : Set α) : A ⊆ A := by
  intro x hx
  exact hx

/-- Mutual inclusion implies equality of sets. -/
theorem subset_antisymmetric {α : Type*} {A B : Set α}
    (hAB : A ⊆ B) (hBA : B ⊆ A) : A = B := by
  ext x
  constructor
  · intro hxA
    exact hAB hxA
  · intro hxB
    exact hBA hxB

/-- Inclusion of sets is transitive. -/
theorem subset_transitive {α : Type*} {A B C : Set α}
    (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hxA
  exact hBC (hAB hxA)

/-- Union of sets is commutative. -/
theorem union_commutative {α : Type*} (A B : Set α) : A ∪ B = B ∪ A := by
  ext x
  constructor
  · rintro (hxA | hxB)
    · exact Or.inr hxA
    · exact Or.inl hxB
  · rintro (hxB | hxA)
    · exact Or.inr hxB
    · exact Or.inl hxA

/-- Union of sets is associative. -/
theorem union_associative {α : Type*} (A B C : Set α) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  constructor
  · rintro ((hxA | hxB) | hxC)
    · exact Or.inl hxA
    · exact Or.inr (Or.inl hxB)
    · exact Or.inr (Or.inr hxC)
  · rintro (hxA | hxB | hxC)
    · exact Or.inl (Or.inl hxA)
    · exact Or.inl (Or.inr hxB)
    · exact Or.inr hxC

/-- The left operand of a union is contained in the union. -/
theorem subset_union_left {α : Type*} (A B : Set α) : A ⊆ A ∪ B := by
  intro x hxA
  exact Or.inl hxA

/-- The right operand of a union is contained in the union. -/
theorem subset_union_right {α : Type*} (A B : Set α) : B ⊆ A ∪ B := by
  intro x hxB
  exact Or.inr hxB

/-- A union equals its right operand exactly when the left is contained in the right. -/
theorem union_eq_right_iff_subset {α : Type*} (A B : Set α) :
    A ⊆ B ↔ A ∪ B = B := by
  constructor
  · intro hAB
    ext x
    constructor
    · rintro (hxA | hxB)
      · exact hAB hxA
      · exact hxB
    · intro hxB
      exact Or.inr hxB
  · intro hUnion x hxA
    have hxUnion : x ∈ A ∪ B := Or.inl hxA
    rw [hUnion] at hxUnion
    exact hxUnion

/-- A union equals its left operand exactly when the right is contained in the left. -/
theorem union_eq_left_iff_subset {α : Type*} (A B : Set α) :
    B ⊆ A ↔ A ∪ B = A := by
  constructor
  · intro hBA
    ext x
    constructor
    · rintro (hxA | hxB)
      · exact hxA
      · exact hBA hxB
    · intro hxA
      exact Or.inl hxA
  · intro hUnion x hxB
    have hxUnion : x ∈ A ∪ B := Or.inr hxB
    rw [hUnion] at hxUnion
    exact hxUnion

/-- Intersection of sets is commutative. -/
theorem inter_commutative {α : Type*} (A B : Set α) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · rintro ⟨hxA, hxB⟩
    exact ⟨hxB, hxA⟩
  · rintro ⟨hxB, hxA⟩
    exact ⟨hxA, hxB⟩

end HighSchoolMathLean.SetTheory
