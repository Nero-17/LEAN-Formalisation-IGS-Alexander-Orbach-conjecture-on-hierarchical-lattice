import IGSIII34.Diffusion.CompactUniformGlobalCouplingCompletion
import IGSIII34.Diffusion.PathWeakAECouplingTransferCompletion
import IGSIII34.Diffusion.SkorokhodCadlagCarrierTransportCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal

def skorokhodCadlagContinuousCarrierMapCompletion
    {First Second : Type*} [MetricSpace First] [CompactSpace First]
    [MetricSpace Second] [CompactSpace Second]
    (map : First → Second) (continuous : Continuous map)
    (path : SkorokhodCadlagPathCompletion First) : SkorokhodCadlagPathCompletion Second :=
  ⟨skorokhodGlobalCarrierMapCompletion map path.val,
    skorokhodGlobalCarrierMap_cadlag_completion map continuous path.val path.property⟩

theorem skorokhodCadlagContinuousCarrierMap_continuous_completion
    {First Second : Type*} [MetricSpace First] [CompactSpace First]
    [MetricSpace Second] [CompactSpace Second]
    (map : First → Second) (continuous : Continuous map) :
    Continuous (skorokhodCadlagContinuousCarrierMapCompletion map continuous) :=
  ((skorokhodGlobalCarrierMap_continuous_completion map continuous).comp
    continuous_subtype_val).subtype_mk _

/-- Genuine whole-cadlag weak convergence survives replacing projected
finite paths by paths in one common realization. The sole spatial input
is uniform pointwise displacement of the two placements, not an assumed
path-law convergence in the common space. -/
theorem common_embedding_cadlag_sample_weak_completion
    {Target Ambient : Type*} [MetricSpace Target] [CompactSpace Target]
    [MetricSpace Ambient] [CompactSpace Ambient]
    (Outcomes : ℕ → Type*) [∀ index, MeasurableSpace (Outcomes index)]
    (laws : ∀ index, Measure (Outcomes index)) [∀ index, IsProbabilityMeasure (laws index)]
    (targetEmbedding : Target → Ambient) (targetContinuous : Continuous targetEmbedding)
    (originals : ∀ index, Outcomes index → SkorokhodCadlagPathCompletion Ambient)
    (projections : ∀ index, Outcomes index → SkorokhodCadlagPathCompletion Target)
    (originalsMeasurable : ∀ index, AEMeasurable (originals index) (laws index))
    (projectionsMeasurable : ∀ index, AEMeasurable (projections index) (laws index))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion Target))
    (projectedWeak : Tendsto (fun index =>
      ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Outcomes index)) (projectionsMeasurable index))
      atTop (𝓝 law))
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop,
      ∀ outcome time, dist ((originals index outcome).val time)
        (targetEmbedding ((projections index outcome).val time)) < tolerance) :
    Tendsto (fun index => ProbabilityMeasure.map
      (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Outcomes index)) (originalsMeasurable index)) atTop
      (𝓝 (law.map (skorokhodCadlagContinuousCarrierMap_continuous_completion targetEmbedding
        targetContinuous).measurable.aemeasurable)) := by
  let map := skorokhodCadlagContinuousCarrierMapCompletion targetEmbedding targetContinuous
  have mapContinuous : Continuous map :=
    skorokhodCadlagContinuousCarrierMap_continuous_completion targetEmbedding targetContinuous
  let approximations := fun index outcome => map (projections index outcome)
  have approximationsMeasurable (index : ℕ) : AEMeasurable (approximations index) (laws index) :=
    mapContinuous.measurable.comp_aemeasurable (projectionsMeasurable index)
  have mapIdentity (index : ℕ) :
      ((ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Outcomes index))
        (projectionsMeasurable index)).map mapContinuous.measurable.aemeasurable) =
      ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Outcomes index))
        (approximationsMeasurable index) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact AEMeasurable.map_map_of_aemeasurable mapContinuous.measurable.aemeasurable (projectionsMeasurable index)
  have weakApproximations : Tendsto (fun index =>
      ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Outcomes index))
        (approximationsMeasurable index)) atTop (𝓝 (law.map mapContinuous.measurable.aemeasurable)) := by
    have mapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ law projectedWeak mapContinuous
    exact mapped.congr' (Eventually.of_forall mapIdentity)
  apply probability_ae_sample_weak_transfer_completion laws
    (law : Measure (SkorokhodCadlagPathCompletion Target)) originals approximations map
    originalsMeasurable approximationsMeasurable mapContinuous.measurable.aemeasurable weakApproximations
  intro tolerance error positive errorPositive
  have globalCoupling := compact_uniform_global_coupling_probability_completion
    Outcomes laws (fun index outcome => (originals index outcome).val)
    (fun index outcome => (approximations index outcome).val) (fun horizon spatialTolerance spatialError spatialPositive spatialErrorPositive => by
      filter_upwards [placementClose spatialTolerance spatialPositive] with index close
      refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
      · simpa only [Measure.real, measure_empty, ENNReal.toReal_zero] using spatialErrorPositive.le
      · intro outcome _ time _
        exact (close outcome time).le) tolerance error positive errorPositive
  filter_upwards [globalCoupling] with index coupling
  obtain ⟨bad, measurableBad, probabilityBad, close⟩ := coupling
  exact ⟨bad, measurableBad, probabilityBad, close⟩

end
end IGSIII34.Diffusion
