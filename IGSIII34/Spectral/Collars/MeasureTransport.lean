import IGSIII34.Diffusion.ProbabilityWeakMetricCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped _root_.Topology

theorem probability_levyProkhorov_of_weak
    {Space : Type*} [PseudoMetricSpace Space] [SeparableSpace Space]
    [MeasurableSpace Space] [OpensMeasurableSpace Space]
    {Index : Type*} {filter : Filter Index}
    (measures : Index → ProbabilityMeasure Space) (limitMeasure : ProbabilityMeasure Space)
    (convergence : Tendsto measures filter (𝓝 limitMeasure)) :
    Tendsto (fun index => levyProkhorovEDist (measures index : Measure Space)
      (limitMeasure : Measure Space)) filter (𝓝 0) := by
  have metricLimit := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.continuousAt.tendsto.comp convergence
  exact tendsto_iff_edist_tendsto_0.mp metricLimit

/-- A continuous map transports LP convergence of probabilities into a
separable target, preserving the actual chosen limit measure. -/
theorem levyProkhorovEDist_map_continuous_tendsto_zero
    {First Last : Type*} [PseudoMetricSpace First] [PseudoMetricSpace Last] [SeparableSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (measures : ℕ → Measure First) [∀ depth, IsProbabilityMeasure (measures depth)]
    (limitMeasure : Measure First) [IsProbabilityMeasure limitMeasure]
    (mapping : First → Last) (continuous : Continuous mapping)
    (convergence : Tendsto (fun depth => levyProkhorovEDist (measures depth) limitMeasure) atTop (𝓝 0)) :
    Tendsto (fun depth => levyProkhorovEDist ((measures depth).map mapping) (limitMeasure.map mapping))
      atTop (𝓝 0) := by
  let probabilities : ℕ → ProbabilityMeasure First := fun depth => ⟨measures depth, inferInstance⟩
  let probability : ProbabilityMeasure First := ⟨limitMeasure, inferInstance⟩
  have weak := IGSIII34.Diffusion.probability_weak_of_levyProkhorov_completion probabilities probability convergence
  have mapped : Tendsto
      (fun depth => (probabilities depth).map continuous.measurable.aemeasurable) atTop
      (𝓝 (probability.map continuous.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ probability weak continuous
  exact probability_levyProkhorov_of_weak
    (fun depth => (probabilities depth).map continuous.measurable.aemeasurable)
    (probability.map continuous.measurable.aemeasurable) mapped

end
end IGSIII34.Spectral
