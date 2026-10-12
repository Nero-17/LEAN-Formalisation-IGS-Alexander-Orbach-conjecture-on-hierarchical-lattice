import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal
variable {First Second : Type*} [MetricSpace First] [CompactSpace First]
  [MetricSpace Second] [CompactSpace Second]

def skorokhodCarrierMapCompletion (map : First → Second)
    (path : SkorokhodIntervalPathCompletion First) : SkorokhodIntervalPathCompletion Second :=
  ⟨fun time => map (path time)⟩

theorem skorokhodCarrierMap_continuous_completion
    (map : First → Second) (continuous : Continuous map) :
    Continuous (skorokhodCarrierMapCompletion map) := by
  apply continuous_iff_continuousAt.mpr
  intro path
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  obtain ⟨duration, durationPositive, spatialClose⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous) (tolerance / 2) (by positivity)
  let error := min duration (tolerance / 2)
  have errorPositive : 0 < error := lt_min durationPositive (by positivity)
  filter_upwards [Metric.ball_mem_nhds path errorPositive] with next nearby
  have nearbyEDistance : skorokhodJ1EDistCompletion next path < ENNReal.ofReal error := edist_lt_ofReal.mpr nearby
  obtain ⟨change, changeSmall⟩ := iInf_lt_iff.mp nearbyEDistance
  have transformedBound : edist (skorokhodCarrierMapCompletion map next) (skorokhodCarrierMapCompletion map path) ≤
      ENNReal.ofReal (tolerance / 2) := by
    change skorokhodJ1EDistCompletion _ _ ≤ _
    apply iInf_le_of_le change
    apply max_le
    · apply iSup_le
      intro time
      have timeSmall : edist (change time) time < ENNReal.ofReal error :=
        ((le_iSup (fun next => edist (change next) next) time).trans (le_max_left _ _)).trans_lt changeSmall
      exact timeSmall.le.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
    · apply iSup_le
      intro time
      have spatialSmall : dist (next (change time)) (path time) < duration := by
        have small : edist (next (change time)) (path time) < ENNReal.ofReal error :=
          ((le_iSup (fun time => edist (next (change time)) (path time)) time).trans (le_max_right _ _)).trans_lt changeSmall
        exact (edist_lt_ofReal.mp small).trans_le (min_le_left _ _)
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (spatialClose spatialSmall).le
  have realBound := (edist_le_ofReal (by positivity : 0 ≤ tolerance / 2)).mp transformedBound
  linarith

def skorokhodCarrierHomeomorphCompletion (homeomorph : First ≃ₜ Second) :
    SkorokhodIntervalPathCompletion First ≃ₜ SkorokhodIntervalPathCompletion Second where
  toFun := skorokhodCarrierMapCompletion homeomorph
  invFun := skorokhodCarrierMapCompletion homeomorph.symm
  left_inv path := by
    cases path
    simp only [skorokhodCarrierMapCompletion]
    congr 1
    funext time
    exact homeomorph.symm_apply_apply _
  right_inv path := by
    cases path
    simp only [skorokhodCarrierMapCompletion]
    congr 1
    funext time
    exact homeomorph.apply_symm_apply _
  continuous_toFun := skorokhodCarrierMap_continuous_completion homeomorph homeomorph.continuous
  continuous_invFun := skorokhodCarrierMap_continuous_completion homeomorph.symm homeomorph.symm.continuous

theorem skorokhodCarrierMap_weak_convergence_completion
    (homeomorph : First ≃ₜ Second)
    (laws : ℕ → ProbabilityMeasure (SkorokhodIntervalPathCompletion First))
    (law : ProbabilityMeasure (SkorokhodIntervalPathCompletion First))
    (convergence : Tendsto laws atTop (𝓝 law)) :
    Tendsto (fun index => (laws index).map (skorokhodCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable)
      atTop (𝓝 (law.map (skorokhodCarrierHomeomorphCompletion homeomorph).continuous.measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws law convergence
    (skorokhodCarrierHomeomorphCompletion homeomorph).continuous

end
end IGSIII34.Diffusion

