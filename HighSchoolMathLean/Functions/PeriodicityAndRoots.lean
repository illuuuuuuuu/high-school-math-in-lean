/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Functions.Properties
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace HighSchoolMathLean.Functions

/-- A real function is periodic on `D` when it has a nonzero translation that
preserves both the domain and every function value. -/
def IsPeriodicOn (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∃ T : ℝ, T ≠ 0 ∧ ∀ x ∈ D, x + T ∈ D ∧ f (x + T) = f x

/-- `T` is the least positive period of `f` on `D` when it is a positive
period and no other positive period is smaller. -/
def IsLeastPositivePeriodOn (f : ℝ → ℝ) (D : Set ℝ) (T : ℝ) : Prop :=
  0 < T ∧
    (∀ x ∈ D, x + T ∈ D ∧ f (x + T) = f x) ∧
    ∀ S : ℝ, 0 < S →
      (∀ x ∈ D, x + S ∈ D ∧ f (x + S) = f x) → T ≤ S

/-- A power function on `D` evaluates a chosen real-power operation at a fixed
exponent. The operation is explicit because textbook real powers use
domain-sensitive conventions for negative bases. -/
def IsPowerFunctionOn (power : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (D : Set ℝ) (a : ℝ) : Prop :=
  ∀ x ∈ D, f x = power x a

/-- A compact formal specification of the standard power-function table. It
records the domain, range, parity, and strict monotonicity conclusions for
integer, reduced rational, and irrational exponent classes. -/
def PowerFunctionProperties (f : ℝ → ℝ) (D : Set ℝ) (a : ℝ) : Prop :=
  (a = 0 →
    D = Set.Iio 0 ∪ Set.Ioi 0 ∧
    f '' D = {1} ∧
    (∀ x ∈ D, -x ∈ D → f (-x) = f x) ∧
    ¬ StrictMonoOn f D ∧ ¬ StrictAntiOn f D) ∧
  (∀ n : ℕ, 0 < n → Odd n → a = (n : ℝ) →
    D = Set.univ ∧ f '' D = Set.univ ∧
    (∀ x, f (-x) = -f x) ∧ StrictMono f) ∧
  (∀ n : ℕ, 0 < n → Even n → a = (n : ℝ) →
    D = Set.univ ∧ f '' D = Set.Ici 0 ∧
    (∀ x, f (-x) = f x) ∧
    StrictAntiOn f (Set.Iic 0) ∧ StrictMonoOn f (Set.Ici 0)) ∧
  (∀ n : ℕ, 0 < n → Odd n → a = -(n : ℝ) →
    D = Set.Iio 0 ∪ Set.Ioi 0 ∧
    f '' D = Set.Iio 0 ∪ Set.Ioi 0 ∧
    (∀ x ∈ D, -x ∈ D → f (-x) = -f x) ∧
    StrictAntiOn f (Set.Iio 0) ∧ StrictAntiOn f (Set.Ioi 0)) ∧
  (∀ n : ℕ, 0 < n → Even n → a = -(n : ℝ) →
    D = Set.Iio 0 ∪ Set.Ioi 0 ∧ f '' D = Set.Ioi 0 ∧
    (∀ x ∈ D, -x ∈ D → f (-x) = f x) ∧
    StrictMonoOn f (Set.Iio 0) ∧ StrictAntiOn f (Set.Ioi 0)) ∧
  (∀ p q : ℕ, 0 < p → 0 < q → Nat.Coprime p q → Odd q →
    a = (p : ℝ) / (q : ℝ) →
    D = Set.univ ∧
    (Odd p → f '' D = Set.univ ∧ (∀ x, f (-x) = -f x) ∧ StrictMono f) ∧
    (Even p → f '' D = Set.Ici 0 ∧ (∀ x, f (-x) = f x) ∧
      StrictAntiOn f (Set.Iic 0) ∧ StrictMonoOn f (Set.Ici 0))) ∧
  (∀ p q : ℕ, 0 < p → 0 < q → Nat.Coprime p q → Even q →
    a = (p : ℝ) / (q : ℝ) →
    D = Set.Ici 0 ∧ f '' D = Set.Ici 0 ∧ StrictMonoOn f (Set.Ici 0)) ∧
  (∀ p q : ℕ, 0 < p → 0 < q → Nat.Coprime p q → Odd q →
    a = -((p : ℝ) / (q : ℝ)) →
    D = Set.Iio 0 ∪ Set.Ioi 0 ∧
    (Odd p → f '' D = Set.Iio 0 ∪ Set.Ioi 0 ∧
      (∀ x ∈ D, -x ∈ D → f (-x) = -f x) ∧
      StrictAntiOn f (Set.Iio 0) ∧ StrictAntiOn f (Set.Ioi 0)) ∧
    (Even p → f '' D = Set.Ioi 0 ∧
      (∀ x ∈ D, -x ∈ D → f (-x) = f x) ∧
      StrictMonoOn f (Set.Iio 0) ∧ StrictAntiOn f (Set.Ioi 0))) ∧
  (∀ p q : ℕ, 0 < p → 0 < q → Nat.Coprime p q → Even q →
    a = -((p : ℝ) / (q : ℝ)) →
    D = Set.Ioi 0 ∧ f '' D = Set.Ioi 0 ∧ StrictAntiOn f (Set.Ioi 0)) ∧
  (Irrational a → 0 < a →
    D = Set.Ici 0 ∧ f '' D = Set.Ici 0 ∧ StrictMonoOn f (Set.Ici 0)) ∧
  (Irrational a → a < 0 →
    D = Set.Ioi 0 ∧ f '' D = Set.Ioi 0 ∧ StrictAntiOn f (Set.Ioi 0))

/-- A point is a zero of a real function exactly when the function value is
zero there. -/
def IsFunctionZero (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  f x₀ = 0

/-- A continuous real function whose endpoint values have opposite signs has
a zero strictly between the endpoints. -/
theorem exists_zero_between_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hsign : f a * f b < 0) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  rcases (mul_neg_iff.mp hsign) with h | h
  · have hzero : (0 : ℝ) ∈ Set.Icc (f b) (f a) :=
      ⟨le_of_lt h.2, le_of_lt h.1⟩
    rcases (intermediate_value_Icc' (le_of_lt hab) hf hzero) with ⟨c, hc, hfc⟩
    have hac : a < c := by
      apply lt_of_le_of_ne hc.1
      intro heq
      subst c
      linarith
    have hcb : c < b := by
      apply lt_of_le_of_ne hc.2
      intro heq
      subst c
      linarith
    exact ⟨c, ⟨hac, hcb⟩, hfc⟩
  · have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
      ⟨le_of_lt h.1, le_of_lt h.2⟩
    rcases (intermediate_value_Icc (le_of_lt hab) hf hzero) with ⟨c, hc, hfc⟩
    have hac : a < c := by
      apply lt_of_le_of_ne hc.1
      intro heq
      subst c
      linarith
    have hcb : c < b := by
      apply lt_of_le_of_ne hc.2
      intro heq
      subst c
      linarith
    exact ⟨c, ⟨hac, hcb⟩, hfc⟩

/-- `x` is an `n`th root of `a` when its `n`th natural power equals `a`. -/
def IsNthRoot (n : ℕ) (x a : ℝ) : Prop :=
  x ^ n = a

/-- If an even-degree real root exists, then its radicand is nonnegative. -/
theorem even_root_radicand_nonnegative (n p : ℕ) (x a : ℝ)
    (hn : n = 2 * p) (hroot : IsNthRoot n x a) :
    0 ≤ a := by
  rw [IsNthRoot, hn] at hroot
  rw [← hroot, mul_comm, pow_mul]
  exact sq_nonneg _

/-- Zero is an `n`th root of zero for every positive natural degree. -/
theorem zero_is_nth_root_of_zero (n : ℕ) (hn : 0 < n) :
    IsNthRoot n 0 0 := by
  simp [IsNthRoot, Nat.ne_of_gt hn]

/-- Raising an actual `n`th root to the `n`th power recovers its radicand. -/
theorem nth_power_of_nth_root {n : ℕ} {x a : ℝ}
    (hroot : IsNthRoot n x a) :
    x ^ n = a :=
  hroot

end HighSchoolMathLean.Functions
