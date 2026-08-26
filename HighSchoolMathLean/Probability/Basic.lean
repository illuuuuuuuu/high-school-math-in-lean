/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace HighSchoolMathLean.Probability

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- A random trial has a known set of at least two possible outcomes and may
be repeated; each run returns exactly one possible outcome. -/
structure RandomTrial where
  Outcome : Type*
  possible : Set Outcome
  possible_nonempty : possible.Nonempty
  has_distinct_outcomes : ∃ a ∈ possible, ∃ b ∈ possible, a ≠ b
  run : ℕ → Outcome
  run_mem : ∀ n, run n ∈ possible

/-- The sample space of a random trial is the set of all its possible sample
points. -/
def samplePointSpace (E : RandomTrial) : Set E.Outcome :=
  E.possible

/-- An event is a subset of the sample space. -/
abbrev RandomEvent (Ω : Type*) := Set Ω

/-- The certain event and impossible event are respectively the whole sample
space and the empty set. -/
def certainAndImpossibleEvents (Ω : Type*) : RandomEvent Ω × RandomEvent Ω :=
  (Set.univ, ∅)

/-- Event `B` contains event `A` exactly when occurrence of `A` implies
occurrence of `B` for every sample point. -/
theorem eventContainment_iff {Ω : Type*} {A B : RandomEvent Ω} :
    A ⊆ B ↔ ∀ ω, ω ∈ A → ω ∈ B :=
  Iff.rfl

/-- The union event occurs when at least one of its two constituent events
occurs. -/
def unionEvent {Ω : Type*} (A B : RandomEvent Ω) : RandomEvent Ω :=
  A ∪ B

/-- The intersection event occurs when both constituent events occur. -/
def intersectionEvent {Ω : Type*} (A B : RandomEvent Ω) : RandomEvent Ω :=
  A ∩ B

/-- Two events are mutually exclusive when their intersection is empty. -/
def MutuallyExclusive {Ω : Type*} (A B : RandomEvent Ω) : Prop :=
  A ∩ B = ∅

/-- Two events are complementary when their union is the whole sample space
and their intersection is empty. -/
def ComplementaryEvents {Ω : Type*} (A B : RandomEvent Ω) : Prop :=
  A ∪ B = Set.univ ∧ A ∩ B = ∅

/-- A classical probability model has a finite nonempty sample space and
assigns equal probability to every sample point. -/
structure ClassicalProbabilityModel (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] where
  probability : Measure Ω
  isProbability : IsProbabilityMeasure probability
  equiprobable : ∀ ω,
    probability {ω} = (Fintype.card Ω : ℝ≥0∞)⁻¹

/-- The elementary laws of probability: nonnegativity, normalization,
finite additivity for disjoint events, complements, monotonicity, and the
two-event inclusion-exclusion identity. -/
theorem basicProbabilityProperties
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A B : RandomEvent Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    0 ≤ μ A ∧
    μ Set.univ = 1 ∧
    μ (∅ : Set Ω) = 0 ∧
    (Disjoint A B → μ (A ∪ B) = μ A + μ B) ∧
    (B = Aᶜ → μ B = 1 - μ A ∧ μ A = 1 - μ B) ∧
    (A ⊆ B → μ A ≤ μ B) ∧
    μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := by
  refine ⟨bot_le, measure_univ, measure_empty, ?_, ?_, ?_, ?_⟩
  · intro hdisjoint
    exact measure_union hdisjoint hB
  · intro hcomplement
    subst B
    constructor
    · simpa using measure_compl hA (measure_ne_top μ A)
    · simpa using measure_compl hA.compl (measure_ne_top μ Aᶜ)
  · exact fun hsubset => measure_mono hsubset
  · exact measure_union_add_inter A hB

/-- Two events are independent when the probability of their intersection
is the product of their probabilities. -/
def IndependentEvents {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : RandomEvent Ω) : Prop :=
  μ (A ∩ B) = μ A * μ B

/-- The certain event and the impossible event are each independent of every
event in a probability space. -/
theorem certain_and_impossible_events_independent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : RandomEvent Ω) :
    IndependentEvents μ Set.univ A ∧ IndependentEvents μ ∅ A := by
  simp [IndependentEvents]

/-- Frequency is stable at probability `p` when the sequence of observed
relative frequencies converges to `p`. -/
def FrequencyStability (frequency : ℕ → ℝ) (p : ℝ) : Prop :=
  Tendsto frequency atTop (𝓝 p)

/-- The frequency form of the law of large numbers: stability means that for
every positive tolerance, all sufficiently late frequencies lie within that
tolerance of the probability. -/
theorem frequency_law_of_large_numbers
    {frequency : ℕ → ℝ} {p : ℝ} (h : FrequencyStability frequency p) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |frequency n - p| < ε := by
  intro ε hε
  rcases Metric.tendsto_atTop.1 h ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

/-- A Monte Carlo method generates simulated outcomes and computes an
estimate from any finite initial collection of those outcomes. -/
structure MonteCarloMethod (Ω Result : Type*) where
  simulate : ℕ → Ω
  estimate : {n : ℕ} → (Fin n → Ω) → Result

/-- A pseudo-random sequence is generated deterministically and repeats with
a positive period, while its values may be used as random-like inputs. -/
structure PseudoRandomSequence (α : Type*) where
  value : ℕ → α
  period : ℕ
  period_pos : 0 < period
  periodic : ∀ n, value (n + period) = value n

end HighSchoolMathLean.Probability
