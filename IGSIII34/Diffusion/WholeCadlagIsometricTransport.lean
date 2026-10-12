import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped NNReal PiCountable

variable {First Last : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Last] [CompactSpace Last]

theorem skorokhodIntervalCarrierMap_isometry
    (mapping : First → Last) (isometry : Isometry mapping) :
    Isometry (skorokhodCarrierMapCompletion mapping) := by
  intro first last
  change skorokhodJ1EDistCompletion
    (skorokhodCarrierMapCompletion mapping first)
    (skorokhodCarrierMapCompletion mapping last) =
      skorokhodJ1EDistCompletion first last
  unfold skorokhodJ1EDistCompletion skorokhodTimeChangeErrorCompletion
  simp only [skorokhodCarrierMapCompletion, isometry.edist_eq]

/-- The whole integer-horizon J1 metric is preserved by spatial isometries.
This asserts metric preservation, beyond continuous carrier transport. -/
theorem skorokhodGlobalCarrierMap_isometry
    (mapping : First → Last) (isometry : Isometry mapping) :
    Isometry (skorokhodGlobalCarrierMapCompletion mapping) := by
  apply Isometry.of_dist_eq
  intro first last
  change PiCountable.dist.dist
    (skorokhodIntegerProfileCompletion (skorokhodGlobalCarrierMapCompletion mapping first))
    (skorokhodIntegerProfileCompletion (skorokhodGlobalCarrierMapCompletion mapping last)) =
      PiCountable.dist.dist (skorokhodIntegerProfileCompletion first)
        (skorokhodIntegerProfileCompletion last)
  unfold PiCountable.dist
  apply tsum_congr
  intro horizon
  congr 1
  exact (skorokhodIntervalCarrierMap_isometry mapping isometry).dist_eq
    (skorokhodIntegerProfileCompletion first horizon)
    (skorokhodIntegerProfileCompletion last horizon)

theorem skorokhodCadlagCarrierMap_isometry
    (mapping : First → Last) (isometry : Isometry mapping) :
    Isometry (skorokhodCadlagContinuousCarrierMapCompletion mapping isometry.continuous) := by
  apply Isometry.of_dist_eq
  intro first last
  exact (skorokhodGlobalCarrierMap_isometry mapping isometry).dist_eq first.val last.val

theorem skorokhodCadlagCarrierMap_comp
    {Middle : Type*} [MetricSpace Middle] [CompactSpace Middle]
    (firstMapping : First → Middle) (firstContinuous : Continuous firstMapping)
    (lastMapping : Middle → Last) (lastContinuous : Continuous lastMapping)
    (path : SkorokhodCadlagPathCompletion First) :
    skorokhodCadlagContinuousCarrierMapCompletion lastMapping lastContinuous
      (skorokhodCadlagContinuousCarrierMapCompletion firstMapping firstContinuous path) =
    skorokhodCadlagContinuousCarrierMapCompletion (lastMapping ∘ firstMapping)
      (lastContinuous.comp firstContinuous) path := rfl

end
end IGSIII34.Diffusion
