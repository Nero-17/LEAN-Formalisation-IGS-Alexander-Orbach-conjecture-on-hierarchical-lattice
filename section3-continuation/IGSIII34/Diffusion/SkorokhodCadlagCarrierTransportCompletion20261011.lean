import IGSIII34.Diffusion.SkorokhodGlobalCarrierTransportCompletion20261011
import IGSIII34.Diffusion.SkorokhodCadlagSampleCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open Filter MeasureTheory
open scoped _root_.Topology NNReal
variable {First Second : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Second] [CompactSpace Second]

/-- A compact spatial homeomorphism transports genuine cadlag paths,
preserving the complete integer-horizon J1 topology. -/
def skorokhodCadlagCarrierHomeomorphCompletion20261011 (homeomorph : First ≃ₜ Second) :
    SkorokhodCadlagPathCompletion20261011 First ≃ₜ SkorokhodCadlagPathCompletion20261011 Second where
  toFun path := ⟨skorokhodGlobalCarrierMapCompletion20261011 homeomorph path.val,
    skorokhodGlobalCarrierMap_cadlag_completion20261011 homeomorph homeomorph.continuous path.val path.property⟩
  invFun path := ⟨skorokhodGlobalCarrierMapCompletion20261011 homeomorph.symm path.val,
    skorokhodGlobalCarrierMap_cadlag_completion20261011 homeomorph.symm homeomorph.symm.continuous path.val path.property⟩
  left_inv path := Subtype.ext ((skorokhodGlobalCarrierHomeomorphCompletion20261011 homeomorph).left_inv path.val)
  right_inv path := Subtype.ext ((skorokhodGlobalCarrierHomeomorphCompletion20261011 homeomorph).right_inv path.val)
  continuous_toFun := ((skorokhodGlobalCarrierMap_continuous_completion20261011 homeomorph homeomorph.continuous).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((skorokhodGlobalCarrierMap_continuous_completion20261011 homeomorph.symm homeomorph.symm.continuous).comp
    continuous_subtype_val).subtype_mk _

theorem skorokhodCadlagCarrierMap_weak_convergence_completion20261011
    (homeomorph : First ≃ₜ Second)
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 First))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion20261011 First))
    (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable)
      atTop (𝓝 (law.map (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodCadlagCarrierHomeomorphCompletion20261011 homeomorph).continuous

end
end IGSIII34.Diffusion
