import IGSIII34.Diffusion.CommonEmbeddingCadlagWeakCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open scoped NNReal PiCountable

variable {First Last : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Last] [CompactSpace Last]

theorem skorokhodIntervalCarrierMap_isometry
    (mapping : First → Last) (isometry : Isometry mapping) :
    Isometry (skorokhodCarrierMapCompletion20261011 mapping) := by
  intro first last
  change skorokhodJ1EDistCompletion20261011
    (skorokhodCarrierMapCompletion20261011 mapping first)
    (skorokhodCarrierMapCompletion20261011 mapping last) =
      skorokhodJ1EDistCompletion20261011 first last
  unfold skorokhodJ1EDistCompletion20261011 skorokhodTimeChangeErrorCompletion20261011
  simp only [skorokhodCarrierMapCompletion20261011, isometry.edist_eq]

/-- The whole integer-horizon J1 metric is preserved by spatial isometries.
This asserts metric preservation, beyond continuous carrier transport. -/
theorem skorokhodGlobalCarrierMap_isometry
    (mapping : First → Last) (isometry : Isometry mapping) :
    Isometry (skorokhodGlobalCarrierMapCompletion20261011 mapping) := by
  apply Isometry.of_dist_eq
  intro first last
  change PiCountable.dist.dist
    (skorokhodIntegerProfileCompletion20261011 (skorokhodGlobalCarrierMapCompletion20261011 mapping first))
    (skorokhodIntegerProfileCompletion20261011 (skorokhodGlobalCarrierMapCompletion20261011 mapping last)) =
      PiCountable.dist.dist (skorokhodIntegerProfileCompletion20261011 first)
        (skorokhodIntegerProfileCompletion20261011 last)
  unfold PiCountable.dist
  apply tsum_congr
  intro horizon
  congr 1
  exact (skorokhodIntervalCarrierMap_isometry mapping isometry).dist_eq
    (skorokhodIntegerProfileCompletion20261011 first horizon)
    (skorokhodIntegerProfileCompletion20261011 last horizon)

theorem skorokhodCadlagCarrierMap_isometry
    (mapping : First → Last) (isometry : Isometry mapping) :
    Isometry (skorokhodCadlagContinuousCarrierMapCompletion20261011 mapping isometry.continuous) := by
  apply Isometry.of_dist_eq
  intro first last
  exact (skorokhodGlobalCarrierMap_isometry mapping isometry).dist_eq first.val last.val

theorem skorokhodCadlagCarrierMap_comp
    {Middle : Type*} [MetricSpace Middle] [CompactSpace Middle]
    (firstMapping : First → Middle) (firstContinuous : Continuous firstMapping)
    (lastMapping : Middle → Last) (lastContinuous : Continuous lastMapping)
    (path : SkorokhodCadlagPathCompletion20261011 First) :
    skorokhodCadlagContinuousCarrierMapCompletion20261011 lastMapping lastContinuous
      (skorokhodCadlagContinuousCarrierMapCompletion20261011 firstMapping firstContinuous path) =
    skorokhodCadlagContinuousCarrierMapCompletion20261011 (lastMapping ∘ firstMapping)
      (lastContinuous.comp firstContinuous) path := rfl

end
end IGSIII34.Diffusion
