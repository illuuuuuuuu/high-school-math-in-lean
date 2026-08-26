/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Statistics.Foundations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

namespace HighSchoolMathLean.Statistics

open scoped BigOperators

noncomputable section

/-- A finite family of real numbers models population or sample observations. -/
abbrev Observations (n : ℕ) := Fin n → ℝ

/-- Data have a specified central tendency at a given scale when every
observation lies within that nonnegative radius of the center. -/
def HasCentralTendency {n : ℕ} (data : Observations n)
    (center radius : ℝ) : Prop :=
  0 ≤ radius ∧ ∀ i, |data i - center| ≤ radius

/-- The arithmetic mean of `n` real observations is their sum divided by
`n`; for the empty family Lean's field convention gives value zero. -/
def arithmeticMean {n : ℕ} (data : Observations n) : ℝ :=
  (∑ i, data i) / (n : ℝ)

/-- The median of data already arranged in nondecreasing order. It is the
middle entry for odd length and the mean of the two middle entries for even
positive length; the empty family is assigned zero. -/
def medianOfSorted {n : ℕ} (data : Observations n) : ℝ :=
  if hzero : n = 0 then
    0
  else if Odd n then
    data ⟨n / 2, by omega⟩
  else
    (data ⟨n / 2 - 1, by omega⟩ + data ⟨n / 2, by omega⟩) / 2

/-- The modes are exactly the observed values whose occurrence count is
maximal among all possible values. -/
def modes {α : Type*} [DecidableEq α] {n : ℕ} (data : Fin n → α) : Set α :=
  {value |
    (∃ i, data i = value) ∧
      ∀ other,
        (Finset.univ.filter fun i => data i = other).card ≤
          (Finset.univ.filter fun i => data i = value).card}

/-- A dispersion measure assigns a nonnegative real number to every data set
and vanishes on constant data. -/
structure DispersionMeasure (ι : Type*) where
  toFun : (ι → ℝ) → ℝ
  nonnegative : ∀ data, 0 ≤ toFun data
  constant_eq_zero : ∀ c, toFun (fun _ => c) = 0

/-- The range of a finite real data set is its supremum minus its infimum. -/
def dataRange {n : ℕ} (data : Observations n) : ℝ :=
  sSup (Set.range data) - sInf (Set.range data)

/-- The mean absolute deviation is the mean distance of the observations
from their arithmetic mean. -/
def meanAbsoluteDeviation {n : ℕ} (data : Observations n) : ℝ :=
  (∑ i, |data i - arithmeticMean data|) / (n : ℝ)

/-- The variance is the mean squared deviation from the arithmetic mean. -/
def variance {n : ℕ} (data : Observations n) : ℝ :=
  (∑ i, (data i - arithmeticMean data) ^ 2) / (n : ℝ)

/-- The standard deviation is the nonnegative square root of the variance. -/
def standardDeviation {n : ℕ} (data : Observations n) : ℝ :=
  Real.sqrt (variance data)

end

end HighSchoolMathLean.Statistics
