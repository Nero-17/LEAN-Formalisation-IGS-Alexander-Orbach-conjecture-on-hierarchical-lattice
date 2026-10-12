import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

/-- Uniform displacement of finite placements transports the same weak
mass limit into the already chosen common chemical ambient. -/
theorem common_chemical_measure_transfer
    {Target Ambient : Type*} [MetricSpace Target] [MeasurableSpace Target] [BorelSpace Target]
    [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (Vertices : ℕ → Type*) [∀ depth, MeasurableSpace (Vertices depth)]
    (measures : ∀ depth, ProbabilityMeasure (Vertices depth))
    (projections : ∀ depth, Vertices depth → Target)
    (projectionsMeasurable : ∀ depth, Measurable (projections depth))
    (placements : ∀ depth, Vertices depth → Ambient)
    (placementsMeasurable : ∀ depth, Measurable (placements depth))
    (target : Target → Ambient) (targetContinuous : Continuous target)
    (measure : ProbabilityMeasure Target)
    (projectedWeak : Tendsto (fun depth => (measures depth).map (projectionsMeasurable depth).aemeasurable)
      atTop (𝓝 measure))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (placements depth vertex) (target (projections depth vertex)) < tolerance) :
    Tendsto (fun depth => (measures depth).map (placementsMeasurable depth).aemeasurable)
      atTop (𝓝 (measure.map targetContinuous.measurable.aemeasurable)) := by
  let approximations := fun depth vertex => target (projections depth vertex)
  have approximationsMeasurable : ∀ depth, Measurable (approximations depth) :=
    fun depth => targetContinuous.measurable.comp (projectionsMeasurable depth)
  have mappedWeak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ measure projectedWeak targetContinuous
  have approximationsWeak : Tendsto (fun depth => (measures depth).map (approximationsMeasurable depth).aemeasurable)
      atTop (𝓝 (measure.map targetContinuous.measurable.aemeasurable)) := by
    apply mappedWeak.congr'
    apply Eventually.of_forall
    intro depth
    apply ProbabilityMeasure.toMeasure_injective
    exact AEMeasurable.map_map_of_aemeasurable targetContinuous.measurable.aemeasurable
      (projectionsMeasurable depth).aemeasurable
  apply IGSIII34.Diffusion.probability_ae_sample_weak_transfer_completion
    (fun depth => (measures depth : Measure (Vertices depth))) (measure : Measure Target)
    placements approximations target (fun depth => (placementsMeasurable depth).aemeasurable)
    (fun depth => (approximationsMeasurable depth).aemeasurable) targetContinuous.measurable.aemeasurable approximationsWeak
  intro tolerance error tolerancePositive errorPositive
  filter_upwards [placementClose tolerance tolerancePositive] with depth close
  refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
  · simpa only [Measure.real, measure_empty, ENNReal.toReal_zero] using errorPositive.le
  · intro vertex _
    exact (close vertex).le

end
end IGSIII34.ResistanceLimit
