/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.SolidGeometry.Incidence
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace HighSchoolMathLean.SolidGeometry

open scoped Affine EuclideanGeometry

/-- Two intersecting spatial lines with different directions determine a
unique spatial plane. -/
theorem intersecting_lines_determine_plane
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hl₁ : Module.finrank ℝ l₁.direction = 1)
    (hl₂ : Module.finrank ℝ l₂.direction = 1)
    (hintersect : ∃! P, P ∈ l₁ ∧ P ∈ l₂)
    (hdirection : l₁.direction ≠ l₂.direction) :
    ∃! plane : SpatialPlane, l₁ ≤ plane.1 ∧ l₂ ≤ plane.1 := by
  obtain ⟨P, hP₁, hP₂⟩ := hintersect.exists
  let span := l₁ ⊔ l₂
  have hdirection_span :
      span.direction = l₁.direction ⊔ l₂.direction := by
    exact AffineSubspace.direction_sup_eq_sup_direction hP₁ hP₂
  have hproper : l₁.direction < l₁.direction ⊔ l₂.direction := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hdirection
    have hle : l₂.direction ≤ l₁.direction := by
      rw [heq]
      exact le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hl₂, hl₁])).symm
  have hdim_lower :
      1 < Module.finrank ℝ ↥(l₁.direction ⊔ l₂.direction) := by
    rw [← hl₁]
    exact Submodule.finrank_lt_finrank_of_lt hproper
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq l₁.direction l₂.direction
  rw [hl₁, hl₂] at hdimension
  have hdim_upper :
      Module.finrank ℝ ↥(l₁.direction ⊔ l₂.direction) ≤ 2 := by omega
  have hdim : Module.finrank ℝ span.direction = 2 := by
    rw [hdirection_span]
    omega
  let plane : SpatialPlane := ⟨span, hdim⟩
  refine ⟨plane, ⟨le_sup_left, le_sup_right⟩, ?_⟩
  intro candidate hcandidate
  apply Subtype.ext
  change candidate.1 = span
  have hspan_le : span ≤ candidate.1 := sup_le hcandidate.1 hcandidate.2
  have hdirection_le := AffineSubspace.direction_le hspan_le
  have hdirection_eq := Submodule.eq_of_le_of_finrank_eq hdirection_le (by
    rw [hdim, candidate.property])
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirection_eq
    ⟨P, (le_sup_left : l₁ ≤ l₁ ⊔ l₂) hP₁⟩ hspan_le).symm

/-- Two distinct parallel spatial lines determine a unique spatial plane. -/
theorem parallel_lines_determine_plane
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hl₁ : Module.finrank ℝ l₁.direction = 1)
    (hl₂ : Module.finrank ℝ l₂.direction = 1)
    (hparallel : l₁ ∥ l₂) (hne : l₁ ≠ l₂) :
    ∃! plane : SpatialPlane, l₁ ≤ plane.1 ∧ l₂ ≤ plane.1 := by
  have hl₂_nonempty : (l₂ : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [l₂.nonempty_iff_ne_bot]
    intro heq
    rw [heq, AffineSubspace.direction_bot] at hl₂
    simp at hl₂
  have hl₂_not_le : ¬ l₂ ≤ l₁ := by
    intro hle
    apply hne
    symm
    exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      hparallel.direction_eq.symm hl₂_nonempty hle
  obtain ⟨P, hP₂, hP₁⟩ :=
    (AffineSubspace.not_le_iff_exists l₂ l₁).mp hl₂_not_le
  obtain ⟨plane, hplane, hunique⟩ :=
    point_and_line_determine_plane l₁ hl₁ hP₁
  have hl₂_le : l₂ ≤ plane.1 := by
    intro Q hQ₂
    have hv₂ : Q -ᵥ P ∈ l₂.direction :=
      AffineSubspace.vsub_mem_direction hQ₂ hP₂
    have hv₁ : Q -ᵥ P ∈ l₁.direction := by
      rw [hparallel.direction_eq]
      exact hv₂
    have hvplane : Q -ᵥ P ∈ plane.1.direction :=
      AffineSubspace.direction_le hplane.2 hv₁
    simpa using AffineSubspace.vadd_mem_of_mem_direction hvplane hplane.1
  refine ⟨plane, ⟨hplane.2, hl₂_le⟩, ?_⟩
  intro candidate hcandidate
  exact hunique candidate ⟨hcandidate.2 hP₂, hcandidate.1⟩

/-- Two spatial lines intersect when they have exactly one common point. -/
def IntersectingLines
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃! P, P ∈ l₁ ∧ P ∈ l₂

/-- Two spatial lines are parallel when one is a translate of the other and
their point sets are disjoint. -/
def ParallelLines
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  l₁ ∥ l₂ ∧
    Disjoint (l₁ : Set (EuclideanSpace ℝ (Fin 3)))
      (l₂ : Set (EuclideanSpace ℝ (Fin 3)))

/-- Two spatial lines are skew in the synthetic sense when no spatial plane
contains both of them. -/
def SkewLinesByNoCommonPlane
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ¬ ∃ plane : SpatialPlane, l₁ ≤ plane.1 ∧ l₂ ≤ plane.1

/-- Equivalently in three-dimensional space, skew lines are disjoint and are
not parallel. This predicate records that standard positional definition. -/
def SkewLines
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  Disjoint (l₁ : Set (EuclideanSpace ℝ (Fin 3)))
      (l₂ : Set (EuclideanSpace ℝ (Fin 3))) ∧
    ¬ l₁ ∥ l₂

/-- A line lies in a plane when every point of the line belongs to the plane. -/
def LineInPlane
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (plane : SpatialPlane) : Prop :=
  line ≤ plane.1

/-- A line intersects a plane when they have exactly one common point. -/
def LineIntersectsPlane
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (plane : SpatialPlane) : Prop :=
  ∃! P, P ∈ line ∧ P ∈ plane.1

/-- A line is parallel to a plane when their point sets are disjoint. -/
def LineParallelPlane
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (plane : SpatialPlane) : Prop :=
  Disjoint (line : Set (EuclideanSpace ℝ (Fin 3)))
    (plane.1 : Set (EuclideanSpace ℝ (Fin 3)))

/-- A line is parallel to a plane exactly when every point of the line lies
outside the plane. -/
theorem line_parallel_plane_iff_every_point_outside
    (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (plane : SpatialPlane) :
    LineParallelPlane line plane ↔ ∀ P ∈ line, P ∉ plane.1 := by
  rw [LineParallelPlane, Set.disjoint_left]
  simp only [SetLike.mem_coe]

/-- Two spatial planes are parallel when their point sets are disjoint. -/
def ParallelPlanes (alpha beta : SpatialPlane) : Prop :=
  Disjoint
    (alpha.1 : Set (EuclideanSpace ℝ (Fin 3)))
    (beta.1 : Set (EuclideanSpace ℝ (Fin 3)))

/-- Two spatial planes intersect when their intersection is exactly a
one-dimensional affine subspace. -/
def IntersectingPlanes (alpha beta : SpatialPlane) : Prop :=
  ∃ line :
      {line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) //
        Module.finrank ℝ line.direction = 1},
    line.1 = alpha.1 ⊓ beta.1

/-- Spatial-line parallelism is transitive through a third line. -/
theorem space_line_parallel_criterion
    (a b c : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hac : a ∥ c) (hbc : b ∥ c) :
    a ∥ b :=
  hac.trans hbc.symm

/-- Parallel corresponding sides make two spatial angles equal modulo a
straight angle, expressed as equality of doubled oriented angles. -/
theorem parallel_rays_angle_relation
    (A B C D E F : EuclideanSpace ℝ (Fin 3))
    (hBAED : ∃ r : ℝ, r ≠ 0 ∧ A -ᵥ B = r • (D -ᵥ E))
    (hBCEF : ∃ s : ℝ, s ≠ 0 ∧ C -ᵥ B = s • (F -ᵥ E)) :
    ∠ A B C = ∠ D E F ∨ ∠ A B C + ∠ D E F = Real.pi := by
  obtain ⟨r, hr, hray₁⟩ := hBAED
  obtain ⟨s, hs, hray₂⟩ := hBCEF
  rw [EuclideanGeometry.angle, EuclideanGeometry.angle, hray₁, hray₂]
  rcases lt_or_gt_of_ne hr with hrneg | hrpos
  · rcases lt_or_gt_of_ne hs with hsneg | hspos
    · left
      rw [InnerProductGeometry.angle_smul_left_of_neg _ _ hrneg,
        InnerProductGeometry.angle_smul_right_of_neg _ _ hsneg,
        InnerProductGeometry.angle_neg_neg]
    · right
      rw [InnerProductGeometry.angle_smul_left_of_neg _ _ hrneg,
        InnerProductGeometry.angle_smul_right_of_pos _ _ hspos,
        InnerProductGeometry.angle_neg_left]
      ring
  · rcases lt_or_gt_of_ne hs with hsneg | hspos
    · right
      rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hrpos,
        InnerProductGeometry.angle_smul_right_of_neg _ _ hsneg,
        InnerProductGeometry.angle_neg_right]
      ring
    · left
      rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hrpos,
        InnerProductGeometry.angle_smul_right_of_pos _ _ hspos]

/-- A line not contained in a plane is parallel to that plane if it is
parallel to a line lying in the plane. -/
theorem line_plane_parallel_criterion
    (a b : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (alpha : SpatialPlane)
    (ha_not_le : ¬ a ≤ alpha.1) (hb_le : b ≤ alpha.1)
    (hab : a ∥ b) :
    LineParallelPlane a alpha := by
  rw [LineParallelPlane, Set.disjoint_left]
  intro P hPa hPalpha
  apply ha_not_le
  intro Q hQa
  have hv_a : Q -ᵥ P ∈ a.direction :=
    AffineSubspace.vsub_mem_direction hQa hPa
  have hv_b : Q -ᵥ P ∈ b.direction := by
    rw [← hab.direction_eq]
    exact hv_a
  have hv_alpha : Q -ᵥ P ∈ alpha.1.direction :=
    AffineSubspace.direction_le hb_le hv_b
  simpa using AffineSubspace.vadd_mem_of_mem_direction hv_alpha hPalpha

/-- If a line parallel to a plane lies in a second plane, then it is parallel
to the intersection line of the two planes. -/
theorem line_plane_parallel_property
    (a b : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (alpha beta : SpatialPlane)
    (ha : Module.finrank ℝ a.direction = 1)
    (hb : Module.finrank ℝ b.direction = 1)
    (ha_parallel : LineParallelPlane a alpha)
    (ha_beta : a ≤ beta.1)
    (hb_intersection : b = alpha.1 ⊓ beta.1) :
    ParallelLines a b := by
  have ha_nonempty : (a : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [a.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at ha
    simp at ha
  have hb_nonempty : (b : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [b.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at hb
    simp at hb
  have hb_ne_bot : b ≠ ⊥ := b.nonempty_iff_ne_bot.mp hb_nonempty
  have ha_direction_alpha : a.direction ≤ alpha.1.direction := by
    by_contra hnot
    have hproper :
        alpha.1.direction < alpha.1.direction ⊔ a.direction :=
      lt_of_le_of_ne le_sup_left (by
        intro heq
        apply hnot
        rw [heq]
        exact le_sup_right)
    have hlower :
        2 < Module.finrank ℝ ↥(alpha.1.direction ⊔ a.direction) := by
      calc
        2 = Module.finrank ℝ alpha.1.direction := alpha.property.symm
        _ < Module.finrank ℝ ↥(alpha.1.direction ⊔ a.direction) :=
          Submodule.finrank_lt_finrank_of_lt hproper
    have hupper :
        Module.finrank ℝ ↥(alpha.1.direction ⊔ a.direction) ≤ 3 := by
      simpa [EuclideanSpace, Module.finrank_pi] using
        (Submodule.finrank_le (alpha.1.direction ⊔ a.direction))
    have htop : alpha.1.direction ⊔ a.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        simpa [EuclideanSpace, Module.finrank_pi] using (show
          Module.finrank ℝ ↥(alpha.1.direction ⊔ a.direction) = 3 by omega))
    have halpha_nonempty :
        (alpha.1 : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
      rw [alpha.1.nonempty_iff_ne_bot]
      intro hbot
      have hdim := alpha.property
      rw [hbot, AffineSubspace.direction_bot] at hdim
      simp at hdim
    obtain ⟨P, hPalpha, hPa⟩ :=
      AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
        halpha_nonempty ha_nonempty htop
    exact (Set.disjoint_left.mp ha_parallel) hPa hPalpha
  obtain ⟨P, hPb⟩ := hb_nonempty
  have hPalpha : P ∈ alpha.1 := by
    rw [hb_intersection] at hPb
    exact hPb.1
  have hPbeta : P ∈ beta.1 := by
    rw [hb_intersection] at hPb
    exact hPb.2
  have hb_direction :
      b.direction = alpha.1.direction ⊓ beta.1.direction := by
    rw [hb_intersection]
    exact AffineSubspace.direction_inf_of_mem hPalpha hPbeta
  have ha_direction_b : a.direction ≤ b.direction := by
    rw [hb_direction]
    intro v hv
    exact ⟨ha_direction_alpha hv, AffineSubspace.direction_le ha_beta hv⟩
  have hdirection : a.direction = b.direction :=
    Submodule.eq_of_le_of_finrank_eq ha_direction_b (by rw [ha, hb])
  have ha_ne_bot : a ≠ ⊥ := a.nonempty_iff_ne_bot.mp ha_nonempty
  refine ⟨(AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot).2
    ⟨hdirection, iff_of_false ha_ne_bot hb_ne_bot⟩, ?_⟩
  rw [Set.disjoint_left]
  intro Q hQa hQb
  exact (Set.disjoint_left.mp ha_parallel) hQa (by
    rw [hb_intersection] at hQb
    exact hQb.1)

/-- Two planes are parallel when one contains two intersecting lines, each
parallel to the other plane. -/
theorem plane_plane_parallel_criterion
    (a b : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (alpha beta : SpatialPlane)
    (ha : Module.finrank ℝ a.direction = 1)
    (hb : Module.finrank ℝ b.direction = 1)
    (ha_beta : a ≤ beta.1) (hb_beta : b ≤ beta.1)
    (hdirection : a.direction ≠ b.direction)
    (ha_parallel : LineParallelPlane a alpha)
    (hb_parallel : LineParallelPlane b alpha) :
    ParallelPlanes beta alpha := by
  have line_direction_le_of_parallel :
      ∀ (line : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))),
        Module.finrank ℝ line.direction = 1 →
        LineParallelPlane line alpha → line.direction ≤ alpha.1.direction := by
    intro line hline hparallel
    have hline_nonempty :
        (line : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
      rw [line.nonempty_iff_ne_bot]
      intro hbot
      rw [hbot, AffineSubspace.direction_bot] at hline
      simp at hline
    by_contra hnot
    have hproper :
        alpha.1.direction < alpha.1.direction ⊔ line.direction :=
      lt_of_le_of_ne le_sup_left (by
        intro heq
        apply hnot
        rw [heq]
        exact le_sup_right)
    have hlower :
        2 < Module.finrank ℝ ↥(alpha.1.direction ⊔ line.direction) := by
      calc
        2 = Module.finrank ℝ alpha.1.direction := alpha.property.symm
        _ < Module.finrank ℝ ↥(alpha.1.direction ⊔ line.direction) :=
          Submodule.finrank_lt_finrank_of_lt hproper
    have hupper :
        Module.finrank ℝ ↥(alpha.1.direction ⊔ line.direction) ≤ 3 := by
      simpa [EuclideanSpace, Module.finrank_pi] using
        (Submodule.finrank_le (alpha.1.direction ⊔ line.direction))
    have htop : alpha.1.direction ⊔ line.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        simpa [EuclideanSpace, Module.finrank_pi] using (show
          Module.finrank ℝ ↥(alpha.1.direction ⊔ line.direction) = 3 by omega))
    have halpha_nonempty :
        (alpha.1 : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
      rw [alpha.1.nonempty_iff_ne_bot]
      intro hbot
      have hdim := alpha.property
      rw [hbot, AffineSubspace.direction_bot] at hdim
      simp at hdim
    obtain ⟨P, hPalpha, hPline⟩ :=
      AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
        halpha_nonempty hline_nonempty htop
    exact (Set.disjoint_left.mp hparallel) hPline hPalpha
  have ha_alpha := line_direction_le_of_parallel a ha ha_parallel
  have hb_alpha := line_direction_le_of_parallel b hb hb_parallel
  have hproper : a.direction < a.direction ⊔ b.direction := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hdirection
    have hle : b.direction ≤ a.direction := by
      rw [heq]
      exact le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hb, ha])).symm
  have hlower : 1 < Module.finrank ℝ ↥(a.direction ⊔ b.direction) := by
    rw [← ha]
    exact Submodule.finrank_lt_finrank_of_lt hproper
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq a.direction b.direction
  rw [ha, hb] at hdimension
  have hsup_dim : Module.finrank ℝ ↥(a.direction ⊔ b.direction) = 2 := by omega
  have hsup_beta : a.direction ⊔ b.direction ≤ beta.1.direction :=
    sup_le (AffineSubspace.direction_le ha_beta)
      (AffineSubspace.direction_le hb_beta)
  have hbeta_direction : a.direction ⊔ b.direction = beta.1.direction :=
    Submodule.eq_of_le_of_finrank_eq hsup_beta (by
      rw [hsup_dim, beta.property])
  have hbeta_alpha : beta.1.direction ≤ alpha.1.direction := by
    rw [← hbeta_direction]
    exact sup_le ha_alpha hb_alpha
  have hdirection_planes : beta.1.direction = alpha.1.direction :=
    Submodule.eq_of_le_of_finrank_eq hbeta_alpha (by
      rw [beta.property, alpha.property])
  rw [ParallelPlanes, Set.disjoint_left]
  intro P hPbeta hPalpha
  have hplanes : beta.1 = alpha.1 :=
    AffineSubspace.ext_of_direction_eq hdirection_planes
      ⟨P, hPbeta, hPalpha⟩
  have ha_nonempty : (a : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [a.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at ha
    simp at ha
  obtain ⟨Q, hQa⟩ := ha_nonempty
  exact (Set.disjoint_left.mp ha_parallel) hQa (by
    rw [← hplanes]
    exact ha_beta hQa)

/-- Intersecting two parallel planes by a third plane produces parallel
intersection lines. -/
theorem plane_plane_parallel_property
    (alpha beta gamma : SpatialPlane)
    (a b : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (ha : Module.finrank ℝ a.direction = 1)
    (hb : Module.finrank ℝ b.direction = 1)
    (hplanes : ParallelPlanes alpha beta)
    (ha_intersection : a = alpha.1 ⊓ gamma.1)
    (hb_intersection : b = beta.1 ⊓ gamma.1) :
    ParallelLines a b := by
  have halpha_nonempty :
      (alpha.1 : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [alpha.1.nonempty_iff_ne_bot]
    intro hbot
    have hdim := alpha.property
    rw [hbot, AffineSubspace.direction_bot] at hdim
    simp at hdim
  have hbeta_nonempty :
      (beta.1 : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [beta.1.nonempty_iff_ne_bot]
    intro hbot
    have hdim := beta.property
    rw [hbot, AffineSubspace.direction_bot] at hdim
    simp at hdim
  have hdirection_planes : alpha.1.direction = beta.1.direction := by
    by_contra hne
    have hbeta_not_le : ¬ beta.1.direction ≤ alpha.1.direction := by
      intro hle
      have heq := Submodule.eq_of_le_of_finrank_eq hle (by
        rw [beta.property, alpha.property])
      exact hne heq.symm
    have hproper :
        alpha.1.direction < alpha.1.direction ⊔ beta.1.direction :=
      lt_of_le_of_ne le_sup_left (by
        intro heq
        apply hbeta_not_le
        rw [heq]
        exact le_sup_right)
    have hlower :
        2 < Module.finrank ℝ ↥(alpha.1.direction ⊔ beta.1.direction) := by
      calc
        2 = Module.finrank ℝ alpha.1.direction := alpha.property.symm
        _ < Module.finrank ℝ ↥(alpha.1.direction ⊔ beta.1.direction) :=
          Submodule.finrank_lt_finrank_of_lt hproper
    have hupper :
        Module.finrank ℝ ↥(alpha.1.direction ⊔ beta.1.direction) ≤ 3 := by
      simpa [EuclideanSpace, Module.finrank_pi] using
        (Submodule.finrank_le (alpha.1.direction ⊔ beta.1.direction))
    have htop : alpha.1.direction ⊔ beta.1.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        simpa [EuclideanSpace, Module.finrank_pi] using (show
          Module.finrank ℝ ↥(alpha.1.direction ⊔ beta.1.direction) = 3 by omega))
    obtain ⟨P, hPalpha, hPbeta⟩ :=
      AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
        halpha_nonempty hbeta_nonempty htop
    exact (Set.disjoint_left.mp hplanes) hPalpha hPbeta
  have ha_nonempty : (a : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [a.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at ha
    simp at ha
  have hb_nonempty : (b : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    rw [b.nonempty_iff_ne_bot]
    intro hbot
    rw [hbot, AffineSubspace.direction_bot] at hb
    simp at hb
  have ha_ne_bot : a ≠ ⊥ := a.nonempty_iff_ne_bot.mp ha_nonempty
  have hb_ne_bot : b ≠ ⊥ := b.nonempty_iff_ne_bot.mp hb_nonempty
  obtain ⟨P, hPa⟩ := ha_nonempty
  obtain ⟨Q, hQb⟩ := hb_nonempty
  have ha_direction :
      a.direction = alpha.1.direction ⊓ gamma.1.direction := by
    have hPalpha : P ∈ alpha.1 := by
      rw [ha_intersection] at hPa
      exact hPa.1
    have hPgamma : P ∈ gamma.1 := by
      rw [ha_intersection] at hPa
      exact hPa.2
    rw [ha_intersection]
    exact AffineSubspace.direction_inf_of_mem hPalpha hPgamma
  have hb_direction :
      b.direction = beta.1.direction ⊓ gamma.1.direction := by
    have hQbeta : Q ∈ beta.1 := by
      rw [hb_intersection] at hQb
      exact hQb.1
    have hQgamma : Q ∈ gamma.1 := by
      rw [hb_intersection] at hQb
      exact hQb.2
    rw [hb_intersection]
    exact AffineSubspace.direction_inf_of_mem hQbeta hQgamma
  have hdirection : a.direction = b.direction := by
    rw [ha_direction, hb_direction, hdirection_planes]
  refine ⟨(AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot).2
    ⟨hdirection, iff_of_false ha_ne_bot hb_ne_bot⟩, ?_⟩
  rw [Set.disjoint_left]
  intro R hRa hRb
  exact (Set.disjoint_left.mp hplanes) (by
    rw [ha_intersection] at hRa
    exact hRa.1) (by
    rw [hb_intersection] at hRb
    exact hRb.1)

/-- Two spatial lines are perpendicular when their direction subspaces are
orthogonal; for nondegenerate lines this is equivalent to a right angle. -/
def PerpendicularLines
    (l₁ l₂ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  l₁.direction ⟂ l₂.direction

/-- A line is perpendicular to a plane exactly when it is perpendicular to
two intersecting lines in that plane with different directions. -/
theorem line_perpendicular_plane_iff
    (l p q : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (alpha : SpatialPlane)
    (hp : Module.finrank ℝ p.direction = 1)
    (hq : Module.finrank ℝ q.direction = 1)
    (hp_alpha : p ≤ alpha.1) (hq_alpha : q ≤ alpha.1)
    (hdirection : p.direction ≠ q.direction) :
    l.direction ⟂ alpha.1.direction ↔
      PerpendicularLines l p ∧ PerpendicularLines l q := by
  have hproper : p.direction < p.direction ⊔ q.direction := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hdirection
    have hle : q.direction ≤ p.direction := by
      rw [heq]
      exact le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hq, hp])).symm
  have hlower : 1 < Module.finrank ℝ ↥(p.direction ⊔ q.direction) := by
    rw [← hp]
    exact Submodule.finrank_lt_finrank_of_lt hproper
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq p.direction q.direction
  rw [hp, hq] at hdimension
  have hsup_dim : Module.finrank ℝ ↥(p.direction ⊔ q.direction) = 2 := by omega
  have hsup_alpha : p.direction ⊔ q.direction ≤ alpha.1.direction :=
    sup_le (AffineSubspace.direction_le hp_alpha)
      (AffineSubspace.direction_le hq_alpha)
  have halpha_direction :
      p.direction ⊔ q.direction = alpha.1.direction :=
    Submodule.eq_of_le_of_finrank_eq hsup_alpha (by
      rw [hsup_dim, alpha.property])
  rw [← halpha_direction, Submodule.isOrtho_sup_right]
  rfl

end HighSchoolMathLean.SolidGeometry
