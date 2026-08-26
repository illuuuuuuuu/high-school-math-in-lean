/-
Copyright (c) 2026 Illusix Liu. All rights reserved.
-/

import Mathlib.Data.Real.Basic

namespace HighSchoolMathLean.Statistics

/-- A set is a population for a study when it contains every object under
investigation. -/
def IsPopulation {α : Type*} (objects population : Set α) : Prop :=
  objects ⊆ population

/-- A sample is a subset selected from a population. -/
def IsSample {α : Type*} (sample population : Set α) : Prop :=
  sample ⊆ population

/-- A real-valued statistic is a function computed from sample data. -/
abbrev Statistic (ι : Type*) := (ι → ℝ) → ℝ

/-- A population parameter is a real-valued function of population data. -/
abbrev PopulationParameter (Ω : Type*) := (Ω → ℝ) → ℝ

/-- A descriptive summary records central location, dispersion, and extreme
values without making an inferential claim about a larger population. -/
structure DescriptiveSummary (ι : Type*) where
  center : Statistic ι
  dispersion : Statistic ι
  minimum : Statistic ι
  maximum : Statistic ι

end HighSchoolMathLean.Statistics
