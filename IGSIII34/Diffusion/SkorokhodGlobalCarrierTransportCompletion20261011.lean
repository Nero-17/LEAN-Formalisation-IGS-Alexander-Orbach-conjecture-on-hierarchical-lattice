import IGSIII34.Diffusion.SkorokhodCarrierTransportCompletion20261011
import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion20261011
import IGSIII34.Diffusion.ActualCadlagPathsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set MeasureTheory
open scoped _root_.Topology NNReal ENNReal
variable {First Second : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Second] [CompactSpace Second]

def skorokhodGlobalCarrierMapCompletion20261011 (map : First → Second)
    (path : SkorokhodGlobalPathCompletion20261011 First) : SkorokhodGlobalPathCompletion20261011 Second :=
  ⟨fun time => map (path time)⟩

theorem skorokhodGlobalCarrierMap_continuous_completion20261011
    (map : First → Second) (continuous : Continuous map) :
    Continuous (skorokhodGlobalCarrierMapCompletion20261011 map) := by
  apply skorokhodGlobal_continuous_iff_completion20261011.mpr
  intro horizon
  exact (skorokhodCarrierMap_continuous_completion20261011 map continuous).comp
    ((continuous_apply horizon).comp skorokhodIntegerProfile_inducing_completion20261011.continuous)

def skorokhodGlobalCarrierHomeomorphCompletion20261011 (homeomorph : First ≃ₜ Second) :
    SkorokhodGlobalPathCompletion20261011 First ≃ₜ SkorokhodGlobalPathCompletion20261011 Second where
  toFun := skorokhodGlobalCarrierMapCompletion20261011 homeomorph
  invFun := skorokhodGlobalCarrierMapCompletion20261011 homeomorph.symm
  left_inv path := by
    cases path
    simp only [skorokhodGlobalCarrierMapCompletion20261011]
    congr 1
    funext time
    exact homeomorph.symm_apply_apply _
  right_inv path := by
    cases path
    simp only [skorokhodGlobalCarrierMapCompletion20261011]
    congr 1
    funext time
    exact homeomorph.apply_symm_apply _
  continuous_toFun := skorokhodGlobalCarrierMap_continuous_completion20261011 homeomorph homeomorph.continuous
  continuous_invFun := skorokhodGlobalCarrierMap_continuous_completion20261011 homeomorph.symm homeomorph.symm.continuous

theorem skorokhodGlobalCarrierMap_weak_convergence_completion20261011
    (homeomorph : First ≃ₜ Second)
    (laws : ℕ → ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011 First))
    (law : ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011 First))
    (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodGlobalCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable)
      atTop (𝓝 (law.map (skorokhodGlobalCarrierHomeomorphCompletion20261011 homeomorph).continuous.measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodGlobalCarrierHomeomorphCompletion20261011 homeomorph).continuous

theorem skorokhodGlobalCarrierMap_cadlag_completion20261011
    (map : First → Second) (continuous : Continuous map)
    (path : SkorokhodGlobalPathCompletion20261011 First)
    (cadlag : SkorokhodCadlagCompletion20261011 path) :
    SkorokhodCadlagCompletion20261011 (skorokhodGlobalCarrierMapCompletion20261011 map path) := by
  constructor
  · intro time
    exact continuous.continuousAt.comp_continuousWithinAt (cadlag.1 time)
  · intro time positive
    obtain ⟨value, limit⟩ := cadlag.2 time positive
    exact ⟨map value, (continuous.tendsto value).comp limit⟩

end
end IGSIII34.Diffusion
