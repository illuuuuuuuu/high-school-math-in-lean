/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.SolidGeometry.Foundations

namespace HighSchoolMathLean.SolidGeometry

/-- A prism is a polyhedron with two faces contained in parallel planes. -/
structure Prism extends Polyhedron where
  lowerBase : SpaceGeometry
  upperBase : SpaceGeometry
  lowerPlane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))
  upperPlane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))
  lowerBase_mem : lowerBase ⊆ lowerPlane
  upperBase_mem : upperBase ⊆ upperPlane
  base_planes_parallel : lowerPlane.direction = upperPlane.direction
  bases_are_faces : lowerBase ∈ faces ∧ upperBase ∈ faces

/-- A pyramid is a polyhedron formed by a planar base and side faces meeting
at an apex outside the base plane. -/
structure Pyramid extends Polyhedron where
  base : SpaceGeometry
  basePlane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))
  apex : EuclideanSpace ℝ (Fin 3)
  sideFaces : List SpaceGeometry
  base_mem : base ⊆ basePlane
  apex_not_mem : apex ∉ basePlane
  faces_eq : faces = base :: sideFaces
  apex_mem_side_faces : ∀ face ∈ sideFaces, apex ∈ face

/-- A pyramidal frustum is a polyhedron bounded by two parallel polygonal
bases and the lateral faces inherited from a pyramid. -/
structure PyramidFrustum extends Polyhedron where
  sourcePyramid : Pyramid
  lowerBase : SpaceGeometry
  upperBase : SpaceGeometry
  lowerPlane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))
  upperPlane : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))
  lowerBase_mem : lowerBase ⊆ lowerPlane
  upperBase_mem : upperBase ⊆ upperPlane
  base_planes_parallel : lowerPlane.direction = upperPlane.direction
  bases_are_faces : lowerBase ∈ faces ∧ upperBase ∈ faces

/-- A closed circular cylinder consists of points whose axial coordinate lies
between zero and its height and whose distance from the axis is at most its
radius. -/
structure CircularCylinder where
  body : SpaceGeometry
  baseCenter : EuclideanSpace ℝ (Fin 3)
  axisDirection : EuclideanSpace ℝ (Fin 3)
  height : ℝ
  radius : ℝ
  axis_unit : ‖axisDirection‖ = 1
  height_nonnegative : 0 ≤ height
  radius_nonnegative : 0 ≤ radius
  body_eq : body =
    {p | let v := p - baseCenter
         let t := inner ℝ axisDirection v
         0 ≤ t ∧ t ≤ height ∧ ‖v - t • axisDirection‖ ≤ radius}

/-- A closed circular cone has linearly decreasing cross-sectional radius
from its base to its apex. -/
structure CircularCone where
  body : SpaceGeometry
  baseCenter : EuclideanSpace ℝ (Fin 3)
  axisDirection : EuclideanSpace ℝ (Fin 3)
  height : ℝ
  radius : ℝ
  axis_unit : ‖axisDirection‖ = 1
  height_positive : 0 < height
  radius_nonnegative : 0 ≤ radius
  body_eq : body =
    {p | let v := p - baseCenter
         let t := inner ℝ axisDirection v
         0 ≤ t ∧ t ≤ height ∧
           ‖v - t • axisDirection‖ ≤ (1 - t / height) * radius}

/-- A closed circular truncated cone interpolates linearly between the radii
of two parallel circular bases. -/
structure CircularTruncatedCone where
  body : SpaceGeometry
  lowerCenter : EuclideanSpace ℝ (Fin 3)
  axisDirection : EuclideanSpace ℝ (Fin 3)
  height : ℝ
  lowerRadius : ℝ
  upperRadius : ℝ
  axis_unit : ‖axisDirection‖ = 1
  height_positive : 0 < height
  lowerRadius_nonnegative : 0 ≤ lowerRadius
  upperRadius_nonnegative : 0 ≤ upperRadius
  body_eq : body =
    {p | let v := p - lowerCenter
         let t := inner ℝ axisDirection v
         0 ≤ t ∧ t ≤ height ∧
           ‖v - t • axisDirection‖ ≤
             lowerRadius + (t / height) * (upperRadius - lowerRadius)}

/-- A closed solid sphere is a closed metric ball in three-dimensional
Euclidean space. -/
structure Sphere where
  body : SpaceGeometry
  center : EuclideanSpace ℝ (Fin 3)
  radius : ℝ
  radius_nonnegative : 0 ≤ radius
  body_eq : body = Metric.closedBall center radius

/-- A simple geometric shape is the body of one of the elementary solid
types developed in this chapter. -/
def SimpleGeometricShape :=
  {s : SpaceGeometry //
    (∃ shape : Prism, shape.body = s) ∨
    (∃ shape : Pyramid, shape.body = s) ∨
    (∃ shape : PyramidFrustum, shape.body = s) ∨
    (∃ shape : CircularCylinder, shape.body = s) ∨
    (∃ shape : CircularCone, shape.body = s) ∨
    (∃ shape : CircularTruncatedCone, shape.body = s) ∨
    (∃ shape : Sphere, shape.body = s)}

/-- A simple combination is the union of a nonempty finite list of elementary
solid bodies. -/
structure SimpleCombination where
  body : SpaceGeometry
  components : List SimpleGeometricShape
  components_nonempty : components ≠ []
  body_eq : body =
    {p | ∃ component ∈ components, p ∈ component.1}

/-- The surface area of a polyhedron is the sum of the areas of its faces,
relative to a supplied face-area functional. -/
noncomputable def polyhedronSurfaceArea
    (polyhedron : Polyhedron) (faceArea : SpaceGeometry → ℝ) : ℝ :=
  (polyhedron.faces.map faceArea).sum

end HighSchoolMathLean.SolidGeometry
