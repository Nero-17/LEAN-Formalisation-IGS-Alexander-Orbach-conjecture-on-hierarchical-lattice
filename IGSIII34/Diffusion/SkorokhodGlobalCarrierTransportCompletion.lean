import IGSIII34.Diffusion.SkorokhodCarrierTransportCompletion
import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion
import IGSIII34.Diffusion.ActualCadlagPathsCompletion

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set MeasureTheory
open scoped _root_.Topology NNReal ENNReal
variable {First Second : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Second] [CompactSpace Second]

def skorokhodGlobalCarrierMapCompletion (map : First → Second)
    (path : SkorokhodGlobalPathCompletion First) : SkorokhodGlobalPathCompletion Second :=
  ⟨fun time => map (path time)⟩

theorem skorokhodGlobalCarrierMap_continuous_completion
    (map : First → Second) (continuous : Continuous map) :
    Continuous (skorokhodGlobalCarrierMapCompletion map) := by
  apply skorokhodGlobal_continuous_iff_completion.mpr
  intro horizon
  exact (skorokhodCarrierMap_continuous_completion map continuous).comp
    ((continuous_apply horizon).comp skorokhodIntegerProfile_inducing_completion.continuous)

def skorokhodGlobalCarrierHomeomorphCompletion (homeomorph : First ≃ₜ Second) :
    SkorokhodGlobalPathCompletion First ≃ₜ SkorokhodGlobalPathCompletion Second where
  toFun := skorokhodGlobalCarrierMapCompletion homeomorph
  invFun := skorokhodGlobalCarrierMapCompletion homeomorph.symm
  left_inv path := by
    cases path
    simp only [skorokhodGlobalCarrierMapCompletion]
    congr 1
    funext time
    exact homeomorph.symm_apply_apply _
  right_inv path := by
    cases path
    simp only [skorokhodGlobalCarrierMapCompletion]
    congr 1
    funext time
    exact homeomorph.apply_symm_apply _
  continuous_toFun := skorokhodGlobalCarrierMap_continuous_completion homeomorph homeomorph.continuous
  continuous_invFun := skorokhodGlobalCarrierMap_continuous_completion homeomorph.symm homeomorph.symm.continuous

theorem skorokhodGlobalCarrierMap_weak_convergence_completion
    (homeomorph : First ≃ₜ Second)
    (laws : ℕ → ProbabilityMeasure (SkorokhodGlobalPathCompletion First))
    (law : ProbabilityMeasure (SkorokhodGlobalPathCompletion First))
    (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodGlobalCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable)
      atTop (𝓝 (law.map (skorokhodGlobalCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodGlobalCarrierHomeomorphCompletion homeomorph).continuous

theorem skorokhodGlobalCarrierMap_cadlag_completion
    (map : First → Second) (continuous : Continuous map)
    (path : SkorokhodGlobalPathCompletion First)
    (cadlag : SkorokhodCadlagCompletion path) :
    SkorokhodCadlagCompletion (skorokhodGlobalCarrierMapCompletion map path) := by
  constructor
  · intro time
    exact continuous.continuousAt.comp_continuousWithinAt (cadlag.1 time)
  · intro time positive
    obtain ⟨value, limit⟩ := cadlag.2 time positive
    exact ⟨map value, (continuous.tendsto value).comp limit⟩

end
end IGSIII34.Diffusion
