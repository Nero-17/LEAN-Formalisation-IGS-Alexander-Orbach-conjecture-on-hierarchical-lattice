import IGSIII34.Diffusion.SkorokhodGlobalCarrierTransportCompletion
import IGSIII34.Diffusion.SkorokhodCadlagSampleCompletion

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
def skorokhodCadlagCarrierHomeomorphCompletion (homeomorph : First ≃ₜ Second) :
    SkorokhodCadlagPathCompletion First ≃ₜ SkorokhodCadlagPathCompletion Second where
  toFun path := ⟨skorokhodGlobalCarrierMapCompletion homeomorph path.val,
    skorokhodGlobalCarrierMap_cadlag_completion homeomorph homeomorph.continuous path.val path.property⟩
  invFun path := ⟨skorokhodGlobalCarrierMapCompletion homeomorph.symm path.val,
    skorokhodGlobalCarrierMap_cadlag_completion homeomorph.symm homeomorph.symm.continuous path.val path.property⟩
  left_inv path := Subtype.ext ((skorokhodGlobalCarrierHomeomorphCompletion homeomorph).left_inv path.val)
  right_inv path := Subtype.ext ((skorokhodGlobalCarrierHomeomorphCompletion homeomorph).right_inv path.val)
  continuous_toFun := ((skorokhodGlobalCarrierMap_continuous_completion homeomorph homeomorph.continuous).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((skorokhodGlobalCarrierMap_continuous_completion homeomorph.symm homeomorph.symm.continuous).comp
    continuous_subtype_val).subtype_mk _

theorem skorokhodCadlagCarrierMap_weak_convergence_completion
    (homeomorph : First ≃ₜ Second)
    (laws : ℕ → ProbabilityMeasure (SkorokhodCadlagPathCompletion First))
    (law : ProbabilityMeasure (SkorokhodCadlagPathCompletion First))
    (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable)
      atTop (𝓝 (law.map (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodCadlagCarrierHomeomorphCompletion homeomorph).continuous

end
end IGSIII34.Diffusion
