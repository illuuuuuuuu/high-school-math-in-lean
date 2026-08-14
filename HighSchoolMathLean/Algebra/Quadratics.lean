/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Tactic

namespace HighSchoolMathLean.Algebra

/-- A quadratic equation over the real numbers, with a nonzero leading coefficient. -/
structure QuadraticEquation where
  a : ℝ
  b : ℝ
  c : ℝ
  leading_ne_zero : a ≠ 0

/-- A real number is a root of a quadratic equation when it makes its polynomial zero. -/
def QuadraticEquation.IsRoot (q : QuadraticEquation) (x : ℝ) : Prop :=
  q.a * x ^ 2 + q.b * x + q.c = 0

/-- The discriminant of a real quadratic equation. -/
def QuadraticEquation.discriminant (q : QuadraticEquation) : ℝ :=
  q.b ^ 2 - 4 * q.a * q.c

/-- The sign of the discriminant classifies the real roots of a quadratic equation.
In the zero-discriminant case, the repeated root is represented by its unique real value. -/
theorem discriminant_real_root_classification (q : QuadraticEquation) :
    (q.discriminant > 0 ↔
      ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ q.IsRoot x₁ ∧ q.IsRoot x₂) ∧
    (q.discriminant = 0 ↔ ∃! x : ℝ, q.IsRoot x) ∧
    (q.discriminant < 0 ↔ ∀ x : ℝ, ¬q.IsRoot x) := by
  have hroot_square (x : ℝ) :
      q.IsRoot x ↔ (2 * q.a * x + q.b) ^ 2 = q.discriminant := by
    have hid : (2 * q.a * x + q.b) ^ 2 - q.discriminant =
        4 * q.a * (q.a * x ^ 2 + q.b * x + q.c) := by
      unfold QuadraticEquation.discriminant
      ring
    constructor
    · intro hx
      unfold QuadraticEquation.IsRoot at hx
      have hzero : (2 * q.a * x + q.b) ^ 2 - q.discriminant = 0 := by
        calc
          (2 * q.a * x + q.b) ^ 2 - q.discriminant =
              4 * q.a * (q.a * x ^ 2 + q.b * x + q.c) := hid
          _ = 0 := by rw [hx]; ring
      exact sub_eq_zero.mp hzero
    · intro hsquare
      have hproduct : (4 * q.a) * (q.a * x ^ 2 + q.b * x + q.c) = 0 := by
        calc
          (4 * q.a) * (q.a * x ^ 2 + q.b * x + q.c) =
              (2 * q.a * x + q.b) ^ 2 - q.discriminant := hid.symm
          _ = 0 := sub_eq_zero.mpr hsquare
      have hcoefficient : (4 : ℝ) * q.a ≠ 0 :=
        mul_ne_zero (by norm_num) q.leading_ne_zero
      have hpolynomial : q.a * x ^ 2 + q.b * x + q.c = 0 :=
        (mul_eq_zero.mp hproduct).resolve_left hcoefficient
      exact hpolynomial
  have hpositive : q.discriminant > 0 ↔
      ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ q.IsRoot x₁ ∧ q.IsRoot x₂ := by
    constructor
    · intro hdisc
      let s : ℝ := Real.sqrt q.discriminant
      let x₁ : ℝ := (-q.b - s) / (2 * q.a)
      let x₂ : ℝ := (-q.b + s) / (2 * q.a)
      have hs_pos : 0 < s := by
        dsimp [s]
        exact Real.sqrt_pos.2 hdisc
      have hs_sq : s ^ 2 = q.discriminant := by
        dsimp [s]
        exact Real.sq_sqrt hdisc.le
      have htwo_a : (2 : ℝ) * q.a ≠ 0 :=
        mul_ne_zero (by norm_num) q.leading_ne_zero
      have hlinear₁ : 2 * q.a * x₁ + q.b = -s := by
        have hmul : x₁ * (2 * q.a) = -q.b - s := by
          dsimp [x₁]
          field_simp [q.leading_ne_zero]
        nlinarith
      have hlinear₂ : 2 * q.a * x₂ + q.b = s := by
        have hmul : x₂ * (2 * q.a) = -q.b + s := by
          dsimp [x₂]
          field_simp [q.leading_ne_zero]
        nlinarith
      refine ⟨x₁, x₂, ?_, (hroot_square x₁).2 ?_, (hroot_square x₂).2 ?_⟩
      · intro heq
        have hsame := congrArg (fun x : ℝ => 2 * q.a * x + q.b) heq
        change 2 * q.a * x₁ + q.b = 2 * q.a * x₂ + q.b at hsame
        rw [hlinear₁, hlinear₂] at hsame
        nlinarith
      · rw [hlinear₁]
        nlinarith
      · rw [hlinear₂]
        nlinarith
    · rintro ⟨x₁, x₂, hne, hx₁, hx₂⟩
      have hsquare₁ := (hroot_square x₁).1 hx₁
      have hsquare₂ := (hroot_square x₂).1 hx₂
      have hnonneg : 0 ≤ q.discriminant := by
        nlinarith [sq_nonneg (2 * q.a * x₁ + q.b)]
      have hdisc_ne : q.discriminant ≠ 0 := by
        intro hzero
        have hlinear₁ : 2 * q.a * x₁ + q.b = 0 := by
          nlinarith [sq_nonneg (2 * q.a * x₁ + q.b)]
        have hlinear₂ : 2 * q.a * x₂ + q.b = 0 := by
          nlinarith [sq_nonneg (2 * q.a * x₂ + q.b)]
        have hproduct : (2 * q.a) * (x₁ - x₂) = 0 := by
          nlinarith
        have htwo_a : (2 : ℝ) * q.a ≠ 0 :=
          mul_ne_zero (by norm_num) q.leading_ne_zero
        have : x₁ - x₂ = 0 := (mul_eq_zero.mp hproduct).resolve_left htwo_a
        exact hne (sub_eq_zero.mp this)
      exact lt_of_le_of_ne hnonneg (Ne.symm hdisc_ne)
  have hzero : q.discriminant = 0 ↔ ∃! x : ℝ, q.IsRoot x := by
    constructor
    · intro hdisc
      let x₀ : ℝ := -q.b / (2 * q.a)
      have htwo_a : (2 : ℝ) * q.a ≠ 0 :=
        mul_ne_zero (by norm_num) q.leading_ne_zero
      have hlinear₀ : 2 * q.a * x₀ + q.b = 0 := by
        dsimp [x₀]
        field_simp [htwo_a]
        ring
      refine ⟨x₀, (hroot_square x₀).2 ?_, ?_⟩
      · rw [hlinear₀, hdisc]
        norm_num
      · intro y hy
        have hy_square := (hroot_square y).1 hy
        have hy_linear : 2 * q.a * y + q.b = 0 := by
          rw [hdisc] at hy_square
          nlinarith [sq_nonneg (2 * q.a * y + q.b)]
        have hproduct : (2 * q.a) * (y - x₀) = 0 := by
          nlinarith
        have : y - x₀ = 0 := (mul_eq_zero.mp hproduct).resolve_left htwo_a
        exact sub_eq_zero.mp this
    · rintro ⟨r, hr, hunique⟩
      have hr_square := (hroot_square r).1 hr
      have hnonneg : 0 ≤ q.discriminant := by
        nlinarith [sq_nonneg (2 * q.a * r + q.b)]
      by_contra hdisc_ne
      have hdisc_pos : q.discriminant > 0 :=
        lt_of_le_of_ne hnonneg (Ne.symm hdisc_ne)
      rcases hpositive.mp hdisc_pos with ⟨x₁, x₂, hne, hx₁, hx₂⟩
      have hx₁r := hunique x₁ hx₁
      have hx₂r := hunique x₂ hx₂
      exact hne (hx₁r.trans hx₂r.symm)
  have hnegative : q.discriminant < 0 ↔ ∀ x : ℝ, ¬q.IsRoot x := by
    constructor
    · intro hdisc x hx
      have hsquare := (hroot_square x).1 hx
      nlinarith [sq_nonneg (2 * q.a * x + q.b)]
    · intro hnoroot
      by_contra hnot_negative
      have hnonneg : 0 ≤ q.discriminant := le_of_not_gt hnot_negative
      rcases hnonneg.eq_or_lt with hdisc_zero | hdisc_pos
      · rcases hzero.mp hdisc_zero.symm with ⟨x, hx, _⟩
        exact hnoroot x hx
      · rcases hpositive.mp hdisc_pos with ⟨x₁, _, _, hx₁, _⟩
        exact hnoroot x₁ hx₁
  exact ⟨hpositive, hzero, hnegative⟩

/-- Vieta's formulas for the two real roots of a quadratic equation.
The final hypothesis includes the repeated-root case explicitly. -/
theorem vieta_for_real_roots (q : QuadraticEquation) (α β : ℝ)
    (hα : q.IsRoot α) (hβ : q.IsRoot β)
    (hpair : α ≠ β ∨ q.discriminant = 0) :
    α + β = -q.b / q.a ∧ α * β = q.c / q.a := by
  unfold QuadraticEquation.IsRoot at hα hβ
  rcases hpair with hne | hdisc
  · have hdifference : (α - β) * (q.a * (α + β) + q.b) = 0 := by
      nlinarith
    have hsum_factor : q.a * (α + β) + q.b = 0 :=
      (mul_eq_zero.mp hdifference).resolve_left (sub_ne_zero.mpr hne)
    have hproduct_factor : q.a * (α * β) - q.c = 0 := by
      nlinarith
    constructor
    · apply (eq_div_iff q.leading_ne_zero).2
      nlinarith
    · apply (eq_div_iff q.leading_ne_zero).2
      nlinarith
  · unfold QuadraticEquation.discriminant at hdisc
    have hlinear : 2 * q.a * α + q.b = 0 := by
      nlinarith [sq_nonneg (2 * q.a * α + q.b)]
    have hsum_factor : q.a * (α + β) + q.b = 0 := by
      have hab : α = β := by
        by_contra hne
        have hdifference : (α - β) * (q.a * (α + β) + q.b) = 0 := by
          nlinarith
        have hsum : q.a * (α + β) + q.b = 0 :=
          (mul_eq_zero.mp hdifference).resolve_left (sub_ne_zero.mpr hne)
        nlinarith
      subst β
      nlinarith
    have hproduct_factor : q.a * (α * β) - q.c = 0 := by
      nlinarith
    constructor
    · apply (eq_div_iff q.leading_ne_zero).2
      nlinarith
    · apply (eq_div_iff q.leading_ne_zero).2
      nlinarith

/-- The monic quadratic built from two real numbers factors with exactly those roots. -/
theorem quadratic_equation_from_roots (α β x : ℝ) :
    x ^ 2 - (α + β) * x + α * β = (x - α) * (x - β) ∧
    (x ^ 2 - (α + β) * x + α * β = 0 ↔ x = α ∨ x = β) := by
  constructor
  · ring
  · constructor
    · intro h
      have hfactor : (x - α) * (x - β) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with hα | hβ
      · exact Or.inl (sub_eq_zero.mp hα)
      · exact Or.inr (sub_eq_zero.mp hβ)
    · rintro (rfl | rfl) <;> ring

/-- Standard identities for the two roots of a monic real quadratic equation. -/
theorem monic_quadratic_root_identities (p q α β : ℝ)
    (hα : α ^ 2 + p * α + q = 0)
    (hβ : β ^ 2 + p * β + q = 0)
    (hpair : α ≠ β ∨ p ^ 2 - 4 * q = 0) :
    α ^ 2 + β ^ 2 = (α + β) ^ 2 - 2 * α * β ∧
    α ^ 2 + β ^ 2 = p ^ 2 - 2 * q ∧
    abs (α - β) = Real.sqrt ((α + β) ^ 2 - 4 * α * β) ∧
    abs (α - β) = Real.sqrt (p ^ 2 - 4 * q) := by
  let equation : QuadraticEquation :=
    { a := 1, b := p, c := q, leading_ne_zero := by norm_num }
  have hα_root : equation.IsRoot α := by
    simpa [equation, QuadraticEquation.IsRoot] using hα
  have hβ_root : equation.IsRoot β := by
    simpa [equation, QuadraticEquation.IsRoot] using hβ
  have hpair_root : α ≠ β ∨ equation.discriminant = 0 := by
    simpa [equation, QuadraticEquation.discriminant] using hpair
  have hvieta := vieta_for_real_roots equation α β hα_root hβ_root hpair_root
  have hsum : α + β = -p := by
    simpa [equation] using hvieta.1
  have hproduct : α * β = q := by
    simpa [equation] using hvieta.2
  have hradicand : (α + β) ^ 2 - 4 * α * β = (α - β) ^ 2 := by
    ring
  have hradicand_nonneg : 0 ≤ (α + β) ^ 2 - 4 * α * β := by
    rw [hradicand]
    positivity
  have hsqrt_sq : (Real.sqrt ((α + β) ^ 2 - 4 * α * β)) ^ 2 =
      (α + β) ^ 2 - 4 * α * β := Real.sq_sqrt hradicand_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((α + β) ^ 2 - 4 * α * β) :=
    Real.sqrt_nonneg _
  have habs_sq : (abs (α - β)) ^ 2 = (α - β) ^ 2 := sq_abs _
  have habs_nonneg : 0 ≤ abs (α - β) := abs_nonneg _
  have habs_sqrt : abs (α - β) = Real.sqrt ((α + β) ^ 2 - 4 * α * β) := by
    nlinarith
  refine ⟨?_, ?_, habs_sqrt, ?_⟩
  · ring
  · nlinarith
  · have hradicands_equal : (α + β) ^ 2 - 4 * α * β = p ^ 2 - 4 * q := by
      rw [hsum, hproduct]
      ring
    rw [← hradicands_equal]
    exact habs_sqrt

/-- A predicate is a one-variable quadratic inequality when it has one of the
three standard comparison forms and its quadratic coefficient is nonzero. -/
def IsOneVariableQuadraticInequality (a b c : ℝ) (P : ℝ → Prop) : Prop :=
  a ≠ 0 ∧
    (P = (fun x => a * x ^ 2 + b * x + c < 0) ∨
      P = (fun x => a * x ^ 2 + b * x + c > 0) ∨
      P = (fun x => a * x ^ 2 + b * x + c ≠ 0))

/-- For a positive leading coefficient, zero discriminant is equivalent to
strict positivity away from the repeated root. -/
theorem positive_quadratic_zero_discriminant_solution_set (a b c : ℝ) (ha : a > 0) :
    b ^ 2 - 4 * a * c = 0 ↔
      {x : ℝ | a * x ^ 2 + b * x + c > 0} =
        {x : ℝ | x ≠ -b / (2 * a)} := by
  let equation : QuadraticEquation :=
    { a := a, b := b, c := c, leading_ne_zero := ha.ne' }
  have hidentity (x : ℝ) :
      4 * a * (a * x ^ 2 + b * x + c) =
        (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
    ring
  have htwo_a : (2 : ℝ) * a ≠ 0 := mul_ne_zero (by norm_num) ha.ne'
  have hvertex_linear : 2 * a * (-b / (2 * a)) + b = 0 := by
    field_simp [htwo_a]
    ring
  constructor
  · intro hdisc
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hpositive hxvertex
      subst x
      have := hidentity (-b / (2 * a))
      nlinarith
    · intro hxne
      have hlinear_ne : 2 * a * x + b ≠ 0 := by
        intro hlinear
        apply hxne
        apply (eq_div_iff htwo_a).2
        nlinarith
      have hsquare_pos : 0 < (2 * a * x + b) ^ 2 := sq_pos_of_ne_zero hlinear_ne
      have := hidentity x
      nlinarith
  · intro hsets
    have hvertex_membership := Set.ext_iff.mp hsets (-b / (2 * a))
    simp only [Set.mem_setOf_eq, ne_eq] at hvertex_membership
    have hvertex_not_positive : ¬(a * (-b / (2 * a)) ^ 2 +
        b * (-b / (2 * a)) + c > 0) := by
      intro hpositive
      exact hvertex_membership.mp hpositive rfl
    have hdisc_nonneg : 0 ≤ b ^ 2 - 4 * a * c := by
      have := hidentity (-b / (2 * a))
      nlinarith
    by_contra hdisc_ne
    have hdisc_pos : 0 < b ^ 2 - 4 * a * c :=
      lt_of_le_of_ne hdisc_nonneg (Ne.symm hdisc_ne)
    have hdisc_equation : equation.discriminant > 0 := by
      simpa [equation, QuadraticEquation.discriminant] using hdisc_pos
    rcases (discriminant_real_root_classification equation).1.mp hdisc_equation with
      ⟨x₁, x₂, hne, hx₁, hx₂⟩
    have hx₁_value : a * x₁ ^ 2 + b * x₁ + c = 0 := by
      simpa [equation, QuadraticEquation.IsRoot] using hx₁
    have hx₂_value : a * x₂ ^ 2 + b * x₂ + c = 0 := by
      simpa [equation, QuadraticEquation.IsRoot] using hx₂
    have hx₁_vertex : x₁ = -b / (2 * a) := by
      by_contra hxne
      have hx₁_positive : a * x₁ ^ 2 + b * x₁ + c > 0 :=
        (Set.ext_iff.mp hsets x₁).mpr hxne
      nlinarith
    have hx₂_vertex : x₂ = -b / (2 * a) := by
      by_contra hxne
      have hx₂_positive : a * x₂ ^ 2 + b * x₂ + c > 0 :=
        (Set.ext_iff.mp hsets x₂).mpr hxne
      nlinarith
    exact hne (hx₁_vertex.trans hx₂_vertex.symm)

/-- For a positive leading coefficient and two ordered roots, positivity holds
exactly outside the interval between the roots. -/
theorem positive_quadratic_two_root_solution_set (a b c x₁ x₂ : ℝ)
    (ha : a > 0) (hx₁ : a * x₁ ^ 2 + b * x₁ + c = 0)
    (hx₂ : a * x₂ ^ 2 + b * x₂ + c = 0) (horder : x₁ < x₂) :
    b ^ 2 - 4 * a * c > 0 ↔
      {x : ℝ | a * x ^ 2 + b * x + c > 0} = Set.Iio x₁ ∪ Set.Ioi x₂ := by
  let equation : QuadraticEquation :=
    { a := a, b := b, c := c, leading_ne_zero := ha.ne' }
  have hx₁_root : equation.IsRoot x₁ := by
    simpa [equation, QuadraticEquation.IsRoot] using hx₁
  have hx₂_root : equation.IsRoot x₂ := by
    simpa [equation, QuadraticEquation.IsRoot] using hx₂
  have hdisc_equation : equation.discriminant > 0 :=
    (discriminant_real_root_classification equation).1.mpr
      ⟨x₁, x₂, ne_of_lt horder, hx₁_root, hx₂_root⟩
  have hdisc : b ^ 2 - 4 * a * c > 0 := by
    simpa [equation, QuadraticEquation.discriminant] using hdisc_equation
  have hvieta := vieta_for_real_roots equation x₁ x₂ hx₁_root hx₂_root
    (Or.inl (ne_of_lt horder))
  have hsum : b = -a * (x₁ + x₂) := by
    have h := hvieta.1
    simp only [equation] at h
    apply (eq_div_iff ha.ne').mp at h
    nlinarith
  have hproduct : c = a * (x₁ * x₂) := by
    have h := hvieta.2
    simp only [equation] at h
    apply (eq_div_iff ha.ne').mp at h
    nlinarith
  have hfactor (x : ℝ) :
      a * x ^ 2 + b * x + c = a * (x - x₁) * (x - x₂) := by
    rw [hsum, hproduct]
    ring
  have hsolution : {x : ℝ | a * x ^ 2 + b * x + c > 0} =
      Set.Iio x₁ ∪ Set.Ioi x₂ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    rw [hfactor]
    constructor
    · intro hpositive
      by_cases hleft : x < x₁
      · exact Or.inl hleft
      · right
        have hx₁_le : x₁ ≤ x := le_of_not_gt hleft
        by_contra hnot_right
        have hx₂_le : x ≤ x₂ := le_of_not_gt hnot_right
        have hprod_nonpos : (x - x₁) * (x - x₂) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx₁_le) (sub_nonpos.mpr hx₂_le)
        nlinarith
    · rintro (hleft | hright)
      · have hx₂ : x < x₂ := lt_trans hleft horder
        exact mul_pos ha (mul_pos_of_neg_of_neg (sub_neg.mpr hleft) (sub_neg.mpr hx₂))
      · have hx₁ : x₁ < x := lt_trans horder hright
        exact mul_pos ha (mul_pos (sub_pos.mpr hx₁) (sub_pos.mpr hright))
  exact ⟨fun _ => hsolution, fun _ => hdisc⟩

/-- For a positive leading coefficient, negative discriminant is equivalent to
strict positivity for every real input. -/
theorem positive_quadratic_negative_discriminant_solution_set (a b c : ℝ) (ha : a > 0) :
    b ^ 2 - 4 * a * c < 0 ↔
      {x : ℝ | a * x ^ 2 + b * x + c > 0} = Set.univ := by
  have hidentity (x : ℝ) :
      4 * a * (a * x ^ 2 + b * x + c) =
        (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
    ring
  have htwo_a : (2 : ℝ) * a ≠ 0 := mul_ne_zero (by norm_num) ha.ne'
  have hvertex_linear : 2 * a * (-b / (2 * a)) + b = 0 := by
    field_simp [htwo_a]
    ring
  constructor
  · intro hdisc
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hsquare_nonneg : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
    have := hidentity x
    nlinarith
  · intro hsets
    have hvertex_membership := Set.ext_iff.mp hsets (-b / (2 * a))
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true] at hvertex_membership
    have := hidentity (-b / (2 * a))
    nlinarith

end HighSchoolMathLean.Algebra
