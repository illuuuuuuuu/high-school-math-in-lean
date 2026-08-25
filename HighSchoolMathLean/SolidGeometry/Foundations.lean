/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

namespace HighSchoolMathLean.SolidGeometry

/-- A spatial geometric body is represented by its set of points in
three-dimensional Euclidean space. -/
abbrev SpaceGeometry := Set (EuclideanSpace ℝ (Fin 3))

/-- A polyhedron consists of finitely described planar faces, edges, and
vertices whose faces cover the boundary of its body. -/
structure Polyhedron where
  body : SpaceGeometry
  faces : List SpaceGeometry
  edges : Finset (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
  vertices : Finset (EuclideanSpace ℝ (Fin 3))
  faces_nonempty : faces ≠ []
  face_coplanar : ∀ face ∈ faces,
    ∃ plane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)), face ⊆ plane
  faces_cover_boundary : ∀ p,
    p ∈ frontier body ↔ ∃ face ∈ faces, p ∈ face

/-- A solid of revolution is a body generated as the orbit of a planar region
under a distance-preserving one-parameter rotation fixing a one-dimensional
axis. -/
structure SolidOfRevolution where
  body : SpaceGeometry
  generatingRegion : SpaceGeometry
  axis : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))
  axis_oneDimensional : Module.finrank ℝ axis.direction = 1
  rotate : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)
  rotate_zero : ∀ p, rotate 0 p = p
  rotate_add : ∀ theta phi p, rotate (theta + phi) p = rotate theta (rotate phi p)
  rotation_preserves_distance : ∀ theta p q,
    dist (rotate theta p) (rotate theta q) = dist p q
  rotation_fixes_axis : ∀ theta p, p ∈ axis → rotate theta p = p
  body_eq_orbit : body =
    {p | ∃ theta q, q ∈ generatingRegion ∧ rotate theta q = p}

end HighSchoolMathLean.SolidGeometry
