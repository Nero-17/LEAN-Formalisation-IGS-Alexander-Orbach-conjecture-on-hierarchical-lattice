import IGSIII34.Diffusion.CountableTimeLimitsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

theorem countableTimeLaws_tendsto_of_unique_subsequential_limits_completion20261011
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (laws : ℕ → ProbabilityMeasure (ℕ → Space)) (target : ProbabilityMeasure (ℕ → Space))
    (unique : ∀ selected : ℕ → ℕ, StrictMono selected →
      ∀ candidate : ProbabilityMeasure (ℕ → Space),
      Tendsto (fun index => laws (selected index)) atTop (𝓝 candidate) → candidate = target) :
    Tendsto laws atTop (𝓝 target) := by
  apply tendsto_def.mpr
  intro set neighborhood
  by_contra failure
  change ¬ ∀ᶠ index in atTop, laws index ∈ set at failure
  have frequent : ∃ᶠ index in atTop, laws index ∉ set := by
    simpa only [Filter.Frequently, not_not] using failure
  obtain ⟨outer, outerStrict, outside⟩ := extraction_of_frequently_atTop frequent
  obtain ⟨candidate, inner, innerStrict, convergence⟩ :=
    countableTimeLaws_subsequence_completion20261011 (fun index => laws (outer index))
  have selectedConvergence : Tendsto (fun index => laws ((outer ∘ inner) index)) atTop (𝓝 candidate) := convergence
  have identified := unique (outer ∘ inner) (outerStrict.comp innerStrict) candidate selectedConvergence
  rw [identified] at selectedConvergence
  have inside := selectedConvergence.eventually neighborhood
  obtain ⟨index, membership⟩ := inside.exists
  exact outside (inner index) membership

end
end IGSIII34.Diffusion
