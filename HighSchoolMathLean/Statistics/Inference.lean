/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import HighSchoolMathLean.Statistics.Descriptive
import Mathlib.Probability.StrongLaw

namespace HighSchoolMathLean.Statistics

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Function ProbabilityTheory Topology

noncomputable section

/-- The coefficient of variation is the standard deviation divided by the
arithmetic mean, expressed as a percentage. -/
def coefficientOfVariation {n : ℕ} (data : Observations n) : ℝ :=
  standardDeviation data / arithmeticMean data * 100

/-- For `4k - 1` sorted observations, the lower quartile is observation `k`
in one-based indexing. -/
def lowerQuartileOfSorted {k : ℕ} (hk : 0 < k)
    (data : Observations (4 * k - 1)) : ℝ :=
  data ⟨k - 1, by omega⟩

/-- For `4k - 1` sorted observations, the upper quartile is observation `3k`
in one-based indexing. -/
def upperQuartileOfSorted {k : ℕ} (hk : 0 < k)
    (data : Observations (4 * k - 1)) : ℝ :=
  data ⟨3 * k - 1, by omega⟩

/-- The interquartile range is the upper quartile minus the lower quartile. -/
def interquartileRangeOfSorted {k : ℕ} (hk : 0 < k)
    (data : Observations (4 * k - 1)) : ℝ :=
  upperQuartileOfSorted hk data - lowerQuartileOfSorted hk data

/-- Inferential statistics turn sample data into a proposed conclusion about
a population. -/
abbrev InferentialStatistics (ι Result : Type*) := (ι → ℝ) → Result

/-- A statistical inference records the population feature being studied and
the rule that infers a proposed feature from sample observations. -/
structure StatisticalInference (ι Ω Feature : Type*) where
  populationFeature : (Ω → ℝ) → Feature
  inferFromSample : InferentialStatistics ι Feature

/-- A parameter-estimation procedure pairs a population parameter with a
real-valued estimator computed from sample data. -/
structure ParameterEstimation (ι Ω : Type*) where
  parameter : PopulationParameter Ω
  estimator : Statistic ι

/-- A hypothesis test specifies a population parameter, a hypothesis about
its value, and the sample-data predicate used to accept that hypothesis. -/
structure HypothesisTest (ι Ω : Type*) where
  parameter : PopulationParameter Ω
  hypothesis : ℝ → Prop
  accepts : (ι → ℝ) → Prop

/-- A point estimate is the single real number returned by an estimator for
the observed sample. -/
def pointEstimate {ι Ω : Type*} (procedure : ParameterEstimation ι Ω)
    (sample : ι → ℝ) : ℝ :=
  procedure.estimator sample

/-- An interval-estimation procedure returns ordered lower and upper bounds
from the sample observations. -/
structure IntervalEstimation (ι Ω : Type*) extends ParameterEstimation ι Ω where
  lower : Statistic ι
  upper : Statistic ι
  lower_le_upper : ∀ sample, lower sample ≤ upper sample

/-- The population mean of a finite real-valued population is its arithmetic
mean. -/
def populationMean {n : ℕ} (population : Observations n) : ℝ :=
  arithmeticMean population

/-- Strong law of large numbers for real observations: independent,
identically distributed, integrable observations have sample means converging
almost surely to the population mean. -/
theorem sampleMean_converges_to_populationMean
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n)
        atTop (𝓝 μ[X 0]) :=
  strong_law_ae_real X hint hindep hident

/-- A sample survey selects a subset of a population and supplies an
inference rule based on the resulting observations. -/
structure SampleSurvey (α Result : Type*) where
  population : Set α
  sample : Set α
  sample_subset : sample ⊆ population
  infer : (sample → ℝ) → Result

/-- If survey statistics converge to a population parameter, then every
positive tolerance is eventually met as sample size grows. -/
theorem sampleSurvey_statistics_approach_parameter
    {statistic : ℕ → ℝ} {parameter : ℝ}
    (h : Tendsto statistic atTop (𝓝 parameter)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |statistic n - parameter| < ε := by
  intro ε hε
  rcases Metric.tendsto_atTop.1 h ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

end

end HighSchoolMathLean.Statistics
