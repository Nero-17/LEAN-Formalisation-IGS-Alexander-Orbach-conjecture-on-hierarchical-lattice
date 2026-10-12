import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

/-- Convergence in the proved Lévy--Prokhorov distance gives genuine weak
convergence of probability measures, without selecting another mass law. -/
theorem probability_weak_of_levyProkhorov_completion
    {Space : Type*} [PseudoMetricSpace Space] [MeasurableSpace Space] [OpensMeasurableSpace Space]
    {Index : Type*} {filter : Filter Index}
    (measures : Index → ProbabilityMeasure Space) (limitMeasure : ProbabilityMeasure Space)
    (convergence : Tendsto (fun index => levyProkhorovEDist (measures index : Measure Space)
      (limitMeasure : Measure Space)) filter (𝓝 0)) : Tendsto measures filter (𝓝 limitMeasure) := by
  have metricLimit : Tendsto (fun index => LevyProkhorov.ofMeasure (measures index)) filter
      (𝓝 (LevyProkhorov.ofMeasure limitMeasure)) := by
    exact tendsto_iff_edist_tendsto_0.mpr convergence
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.continuousAt.tendsto.comp metricLimit

end
end IGSIII34.Diffusion

