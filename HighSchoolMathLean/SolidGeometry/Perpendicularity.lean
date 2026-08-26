/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.SolidGeometry.LineAndPlaneRelations
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace HighSchoolMathLean.SolidGeometry

open scoped Affine

/-- Two distinct spatial lines perpendicular to the same plane are parallel. -/
theorem perpendicular_to_same_plane_parallel
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (alpha : SpatialPlane)
    (hl₁ : Module.finrank ℝ l₁.direction = 1)
    (hl₂ : Module.finrank ℝ l₂.direction = 1)
    (hne : l₁ ≠ l₂)
    (hperp₁ : l₁.direction ⟂ alpha.1.direction)
    (hperp₂ : l₂.direction ⟂ alpha.1.direction) :
    ParallelLines l₁ l₂ := by
  have horth_dim : Module.finrank ℝ alpha.1.directionᗮ = 1 := by
    have hdimension :=
      Submodule.finrank_add_finrank_orthogonal alpha.1.direction
    rw [alpha.property] at hdimension
    have hambient :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp [EuclideanSpace]
    omega
  have hdir₁ : l₁.direction = alpha.1.directionᗮ :=
    Submodule.eq_of_le_of_finrank_eq hperp₁.le (by rw [hl₁, horth_dim])
  have hdir₂ : l₂.direction = alpha.1.directionᗮ :=
    Submodule.eq_of_le_of_finrank_eq hperp₂.le (by rw [hl₂, horth_dim])
  have hdirection : l₁.direction = l₂.direction := hdir₁.trans hdir₂.symm
  have hl₁_nonempty : (l₁ : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [l₁.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at hl₁
    simp at hl₁
  have hl₂_nonempty : (l₂ : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [l₂.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at hl₂
    simp at hl₂
  have hparallel : l₁ ∥ l₂ :=
    (AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot).2
      ⟨hdirection,
        iff_of_false (l₁.nonempty_iff_ne_bot.mp hl₁_nonempty)
          (l₂.nonempty_iff_ne_bot.mp hl₂_nonempty)⟩
  refine ⟨hparallel, ?_⟩
  rw [Set.disjoint_left]
  intro P hP₁ hP₂
  apply hne
  exact AffineSubspace.ext_of_direction_eq hdirection ⟨P, hP₁, hP₂⟩

/-- Through every point there is a unique spatial line perpendicular to a
given spatial plane. -/
theorem unique_perpendicular_line_through_point
    (alpha : SpatialPlane) (P : EuclideanSpace ℝ (Fin 3)) :
    ∃! line :
        {line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) //
          Module.finrank ℝ line.direction = 1},
      P ∈ line.1 ∧ line.1.direction ⟂ alpha.1.direction := by
  have horth_dim : Module.finrank ℝ alpha.1.directionᗮ = 1 := by
    have hdimension :=
      Submodule.finrank_add_finrank_orthogonal alpha.1.direction
    rw [alpha.property] at hdimension
    have hambient :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp [EuclideanSpace]
    omega
  let normalLine :
      {line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) //
        Module.finrank ℝ line.direction = 1} :=
    ⟨AffineSubspace.mk' P alpha.1.directionᗮ, by
      rw [AffineSubspace.direction_mk']
      exact horth_dim⟩
  refine ⟨normalLine, ?_, ?_⟩
  · constructor
    · exact AffineSubspace.self_mem_mk' P alpha.1.directionᗮ
    · rw [AffineSubspace.direction_mk']
      exact Submodule.isOrtho_orthogonal_left alpha.1.direction
  · intro candidate hcandidate
    apply Subtype.ext
    have hdirection_le : candidate.1.direction ≤ alpha.1.directionᗮ :=
      hcandidate.2.le
    have hdirection : candidate.1.direction = alpha.1.directionᗮ :=
      Submodule.eq_of_le_of_finrank_eq hdirection_le (by
        rw [candidate.property, horth_dim])
    exact AffineSubspace.ext_of_direction_eq
      (hdirection.trans (AffineSubspace.direction_mk' P _).symm)
      ⟨P, hcandidate.1, AffineSubspace.self_mem_mk' P _⟩

/-- Through every point there is a unique spatial plane perpendicular to a
given spatial line. -/
theorem unique_perpendicular_plane_through_point
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hline : Module.finrank ℝ line.direction = 1)
    (P : EuclideanSpace ℝ (Fin 3)) :
    ∃! plane : SpatialPlane,
      P ∈ plane.1 ∧ line.direction ⟂ plane.1.direction := by
  have horth_dim : Module.finrank ℝ line.directionᗮ = 2 := by
    have hdimension :=
      Submodule.finrank_add_finrank_orthogonal line.direction
    rw [hline] at hdimension
    have hambient :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp [EuclideanSpace]
    omega
  let normalPlane : SpatialPlane :=
    ⟨AffineSubspace.mk' P line.directionᗮ, by
      rw [AffineSubspace.direction_mk']
      exact horth_dim⟩
  refine ⟨normalPlane, ?_, ?_⟩
  · constructor
    · exact AffineSubspace.self_mem_mk' P line.directionᗮ
    · rw [AffineSubspace.direction_mk']
      exact Submodule.isOrtho_orthogonal_right line.direction
  · intro candidate hcandidate
    apply Subtype.ext
    have hdirection_le : candidate.1.direction ≤ line.directionᗮ :=
      hcandidate.2.symm.le
    have hdirection : candidate.1.direction = line.directionᗮ :=
      Submodule.eq_of_le_of_finrank_eq hdirection_le (by
        rw [candidate.property, horth_dim])
    exact AffineSubspace.ext_of_direction_eq
      (hdirection.trans (AffineSubspace.direction_mk' P _).symm)
      ⟨P, hcandidate.1, AffineSubspace.self_mem_mk' P _⟩

/-- A plane is perpendicular to another plane precisely when it contains the
normal line through one of its points. -/
theorem plane_perpendicular_iff_contains_normal_line
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hline : Module.finrank ℝ line.direction = 1)
    (alpha beta : SpatialPlane) {P : EuclideanSpace ℝ (Fin 3)}
    (hPline : P ∈ line) (hPbeta : P ∈ beta.1)
    (hline_perp : line.direction ⟂ alpha.1.direction) :
    alpha.1.directionᗮ ≤ beta.1.direction ↔ line ≤ beta.1 := by
  have horth_dim : Module.finrank ℝ alpha.1.directionᗮ = 1 := by
    have hdimension :=
      Submodule.finrank_add_finrank_orthogonal alpha.1.direction
    rw [alpha.property] at hdimension
    have hambient :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp [EuclideanSpace]
    omega
  have hline_direction : line.direction = alpha.1.directionᗮ :=
    Submodule.eq_of_le_of_finrank_eq hline_perp.le (by
      rw [hline, horth_dim])
  constructor
  · intro hnormal Q hQline
    have hvline : Q -ᵥ P ∈ line.direction :=
      AffineSubspace.vsub_mem_direction hQline hPline
    have hvbeta : Q -ᵥ P ∈ beta.1.direction := by
      apply hnormal
      rw [← hline_direction]
      exact hvline
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvbeta hPbeta
  · intro hle
    rw [← hline_direction]
    exact AffineSubspace.direction_le hle

/-- For perpendicular planes, a line in either plane perpendicular to their
intersection line is perpendicular to the other plane. -/
theorem perpendicular_planes_intersection_property
    (alpha beta : SpatialPlane)
    (l r : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hl : Module.finrank ℝ l.direction = 1)
    (hr : Module.finrank ℝ r.direction = 1)
    (hl_intersection : l = alpha.1 ⊓ beta.1)
    (hplanes : alpha.1.directionᗮ ≤ beta.1.direction)
    (hlr : PerpendicularLines l r) :
    (r ≤ alpha.1 → r.direction ⟂ beta.1.direction) ∧
      (r ≤ beta.1 → r.direction ⟂ alpha.1.direction) := by
  change l.direction ⟂ r.direction at hlr
  have hl_nonempty : (l : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [l.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at hl
    simp at hl
  obtain ⟨P, hPl⟩ := hl_nonempty
  have hPalpha : P ∈ alpha.1 := by
    rw [hl_intersection] at hPl
    exact hPl.1
  have hPbeta : P ∈ beta.1 := by
    rw [hl_intersection] at hPl
    exact hPl.2
  have hl_direction :
      l.direction = alpha.1.direction ⊓ beta.1.direction := by
    rw [hl_intersection]
    exact AffineSubspace.direction_inf_of_mem hPalpha hPbeta
  have hl_alpha : l.direction ≤ alpha.1.direction := by
    rw [hl_direction]
    exact inf_le_left
  have hl_beta : l.direction ≤ beta.1.direction := by
    rw [hl_direction]
    exact inf_le_right
  have hplanes_symm : beta.1.directionᗮ ≤ alpha.1.direction :=
    (Submodule.orthogonal_le_iff_orthogonal_le).mp hplanes
  have halpha_orth_dim : Module.finrank ℝ alpha.1.directionᗮ = 1 := by
    have hdimension :=
      Submodule.finrank_add_finrank_orthogonal alpha.1.direction
    rw [alpha.property] at hdimension
    have hambient :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp [EuclideanSpace]
    omega
  have hbeta_orth_dim : Module.finrank ℝ beta.1.directionᗮ = 1 := by
    have hdimension :=
      Submodule.finrank_add_finrank_orthogonal beta.1.direction
    rw [beta.property] at hdimension
    have hambient :
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp [EuclideanSpace]
    omega
  constructor
  · intro hr_alpha
    have hcomplement_dim :
        Module.finrank ℝ ↥(l.directionᗮ ⊓ alpha.1.direction) = 1 := by
      have hdimension :=
        Submodule.finrank_add_inf_finrank_orthogonal hl_alpha
      rw [hl, alpha.property] at hdimension
      omega
    have hr_le : r.direction ≤ l.directionᗮ ⊓ alpha.1.direction := by
      intro v hv
      exact ⟨hlr.symm.le hv, AffineSubspace.direction_le hr_alpha hv⟩
    have hr_eq : r.direction = l.directionᗮ ⊓ alpha.1.direction :=
      Submodule.eq_of_le_of_finrank_eq hr_le (by
        rw [hr, hcomplement_dim])
    have hbeta_le :
        beta.1.directionᗮ ≤ l.directionᗮ ⊓ alpha.1.direction := by
      intro v hv
      constructor
      · exact Submodule.orthogonal_le hl_beta hv
      · exact hplanes_symm hv
    have hbeta_eq :
        beta.1.directionᗮ = l.directionᗮ ⊓ alpha.1.direction :=
      Submodule.eq_of_le_of_finrank_eq hbeta_le (by
        rw [hbeta_orth_dim, hcomplement_dim])
    exact (hr_eq.trans hbeta_eq.symm).le
  · intro hr_beta
    have hcomplement_dim :
        Module.finrank ℝ ↥(l.directionᗮ ⊓ beta.1.direction) = 1 := by
      have hdimension :=
        Submodule.finrank_add_inf_finrank_orthogonal hl_beta
      rw [hl, beta.property] at hdimension
      omega
    have hr_le : r.direction ≤ l.directionᗮ ⊓ beta.1.direction := by
      intro v hv
      exact ⟨hlr.symm.le hv, AffineSubspace.direction_le hr_beta hv⟩
    have hr_eq : r.direction = l.directionᗮ ⊓ beta.1.direction :=
      Submodule.eq_of_le_of_finrank_eq hr_le (by
        rw [hr, hcomplement_dim])
    have halpha_le :
        alpha.1.directionᗮ ≤ l.directionᗮ ⊓ beta.1.direction := by
      intro v hv
      constructor
      · exact Submodule.orthogonal_le hl_alpha hv
      · exact hplanes hv
    have halpha_eq :
        alpha.1.directionᗮ = l.directionᗮ ⊓ beta.1.direction :=
      Submodule.eq_of_le_of_finrank_eq halpha_le (by
        rw [halpha_orth_dim, hcomplement_dim])
    exact (hr_eq.trans halpha_eq.symm).le

end HighSchoolMathLean.SolidGeometry
