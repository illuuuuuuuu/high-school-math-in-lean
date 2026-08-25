/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.SolidGeometry.Foundations
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace HighSchoolMathLean.SolidGeometry

/-- A spatial plane is a two-dimensional affine subspace of three-dimensional
Euclidean space. -/
abbrev SpatialPlane :=
  {plane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) //
    Module.finrank ℝ plane.direction = 2}

/-- Three affinely independent points lie in a unique spatial plane. -/
theorem plane_through_noncollinear_points_unique
    (points : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hpoints : AffineIndependent ℝ points) :
    ∃! plane : SpatialPlane, ∀ i, points i ∈ plane.1 := by
  let span := affineSpan ℝ (Set.range points)
  have hdim : Module.finrank ℝ span.direction = 2 := by
    rw [direction_affineSpan]
    exact hpoints.finrank_vectorSpan (by norm_num)
  let plane : SpatialPlane := ⟨span, hdim⟩
  refine ⟨plane, ?_, ?_⟩
  · intro i
    exact mem_affineSpan ℝ (Set.mem_range_self i)
  · intro candidate hcandidate
    apply Subtype.ext
    change candidate.1 = span
    symm
    apply hpoints.affineSpan_eq_of_le_of_card_eq_finrank_add_one
    · apply affineSpan_le_of_subset_coe
      rintro point ⟨i, rfl⟩
      exact hcandidate i
    · norm_num [candidate.property]

/-- The affine line through two points is contained in every plane containing
both points. -/
theorem line_through_two_points_le_plane
    (plane : SpatialPlane) {A B : EuclideanSpace ℝ (Fin 3)}
    (hA : A ∈ plane.1) (hB : B ∈ plane.1) :
    affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 3))) ≤
      plane.1 := by
  apply affineSpan_le_of_subset_coe
  intro point hpoint
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpoint
  rcases hpoint with rfl | rfl
  · exact hA
  · exact hB

/-- Two distinct spatial planes having a common point intersect in a unique
one-dimensional affine subspace through that point. -/
theorem intersecting_planes_have_unique_intersection
    (alpha beta : SpatialPlane) {P : EuclideanSpace ℝ (Fin 3)}
    (halpha : P ∈ alpha.1) (hbeta : P ∈ beta.1)
    (hne : alpha ≠ beta) :
    ∃! line :
        {line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) //
          Module.finrank ℝ line.direction = 1},
      line.1 = alpha.1 ⊓ beta.1 ∧ P ∈ line.1 := by
  have hdirection_ne : alpha.1.direction ≠ beta.1.direction := by
    intro hdirection
    apply hne
    apply Subtype.ext
    exact AffineSubspace.ext_of_direction_eq hdirection
      ⟨P, halpha, hbeta⟩
  have hbeta_not_le : ¬ beta.1.direction ≤ alpha.1.direction := by
    intro hle
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by
      rw [beta.property, alpha.property])
    exact hdirection_ne heq.symm
  have hproper : alpha.1.direction < alpha.1.direction ⊔ beta.1.direction := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hbeta_not_le
    rw [heq]
    exact le_sup_right
  have hsup_lower :
      2 < Module.finrank ℝ ↥(alpha.1.direction ⊔ beta.1.direction) := by
    have h := Submodule.finrank_lt_finrank_of_lt hproper
    omega
  have hsup_upper :
      Module.finrank ℝ ↥(alpha.1.direction ⊔ beta.1.direction) ≤ 3 := by
    simpa [EuclideanSpace, Module.finrank_pi] using
      (Submodule.finrank_le (alpha.1.direction ⊔ beta.1.direction))
  have hintersection_direction :
      Module.finrank ℝ ↥(alpha.1.direction ⊓ beta.1.direction) = 1 := by
    have hdimension :=
      Submodule.finrank_sup_add_finrank_inf_eq alpha.1.direction beta.1.direction
    rw [alpha.property, beta.property] at hdimension
    omega
  have hintersection :
      Module.finrank ℝ (alpha.1 ⊓ beta.1).direction = 1 := by
    rw [AffineSubspace.direction_inf_of_mem halpha hbeta]
    exact hintersection_direction
  let line :
      {line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) //
        Module.finrank ℝ line.direction = 1} :=
    ⟨alpha.1 ⊓ beta.1, hintersection⟩
  refine ⟨line, ⟨rfl, ⟨halpha, hbeta⟩⟩, ?_⟩
  intro candidate hcandidate
  apply Subtype.ext
  exact hcandidate.1

/-- A point outside a one-dimensional affine line and that line determine a
unique spatial plane. -/
theorem point_and_line_determine_plane
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hline : Module.finrank ℝ line.direction = 1)
    {P : EuclideanSpace ℝ (Fin 3)} (hP : P ∉ line) :
    ∃! plane : SpatialPlane, P ∈ plane.1 ∧ line ≤ plane.1 := by
  let span := affineSpan ℝ (Set.insert P (line : Set _))
  have hline_nonempty : (line : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [line.nonempty_iff_ne_bot]
    intro heq
    rw [heq, AffineSubspace.direction_bot] at hline
    simp at hline
  have hline_le : line ≤ span := by
    intro point hpoint
    exact mem_affineSpan ℝ (Set.mem_insert_of_mem P hpoint)
  have hP_mem : P ∈ span :=
    mem_affineSpan ℝ (Set.mem_insert P (line : Set _))
  have hproper : line < span := by
    refine lt_of_le_of_ne hline_le ?_
    intro heq
    apply hP
    rw [heq]
    exact hP_mem
  have hdirection_proper : line.direction < span.direction :=
    AffineSubspace.direction_lt_of_nonempty hproper hline_nonempty
  have hdim_lower : 1 < Module.finrank ℝ span.direction := by
    rw [← hline]
    exact Submodule.finrank_lt_finrank_of_lt hdirection_proper
  have hdim_upper : Module.finrank ℝ span.direction ≤ 2 := by
    rw [direction_affineSpan]
    calc
      Module.finrank ℝ (vectorSpan ℝ (Set.insert P (line : Set _))) ≤
          Module.finrank ℝ line.direction + 1 :=
        finrank_vectorSpan_insert_le line P
      _ = 2 := by omega
  have hdim : Module.finrank ℝ span.direction = 2 := by omega
  let plane : SpatialPlane := ⟨span, hdim⟩
  refine ⟨plane, ⟨hP_mem, hline_le⟩, ?_⟩
  intro candidate hcandidate
  apply Subtype.ext
  change candidate.1 = span
  have hspan_le : span ≤ candidate.1 := by
    apply affineSpan_le_of_subset_coe
    intro point hpoint
    rcases hpoint with (rfl | hpoint)
    · exact hcandidate.1
    · exact hcandidate.2 hpoint
  have hdirection_le := AffineSubspace.direction_le hspan_le
  have hdirection_eq := Submodule.eq_of_le_of_finrank_eq hdirection_le (by
    rw [hdim, candidate.property])
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirection_eq
    ⟨P, hP_mem⟩ hspan_le).symm

end HighSchoolMathLean.SolidGeometry
