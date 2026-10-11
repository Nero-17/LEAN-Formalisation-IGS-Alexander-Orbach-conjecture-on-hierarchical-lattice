import IGSIII34.Diffusion.PathWeakAEReconstructionCompletion20261011
import IGSIII34.Diffusion.SkorokhodGlobalGridErrorCompletion20261011
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space Outcome : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Outcome]

/-- Finite observations and actual physical-time modulus probabilities
imply weak convergence of the whole full-time path laws. The metric uses
genuine J1 on every integer horizon; its summable tail is controlled in
the proof. No separability of the ambient raw-path space is assumed. -/
theorem skorokhodGlobal_ae_weak_of_finite_marginals_and_modulus_completion20261011
    (Samples : ℕ → Type*) [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index)) [∀ index, IsProbabilityMeasure (laws index)]
    (samples : ∀ index, Samples index → SkorokhodGlobalPathCompletion20261011 Space)
    (samplesMeasurable : ∀ index, AEMeasurable (samples index) (laws index))
    (sampleEvaluations : ∀ index time, Measurable (fun outcome => samples index outcome time))
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time))
    (finiteMarginals : ∀ horizon grid,
      Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
        (show AEMeasurable (fun outcome => fun coordinate : Fin (grid+2) =>
          samples index outcome (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid coordinate)) _ from
          (measurable_pi_lambda _ fun coordinate => sampleEvaluations index _).aemeasurable)) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
          (show AEMeasurable (fun outcome => fun coordinate : Fin (grid+2) =>
            sample outcome (skorokhodGlobalRegularGridPointCompletion20261011 horizon grid coordinate)) law from
            (measurable_pi_lambda _ fun coordinate => evaluations _).aemeasurable))))
    (modulus : ∀ horizon tolerance error, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ index in atTop,
        ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome, outcome ∉ bad → ∀ first second : ℝ≥0,
            first ≤ horizon+1 → second ≤ horizon+1 → dist first second < duration →
              dist (samples index outcome first) (samples index outcome second) ≤ tolerance) :
    Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
      (samplesMeasurable index)) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
        (continuousGlobalFamily_measurable_completion20261011 sample sampleContinuous evaluations).aemeasurable)) := by
  let reconstructions := fun code index (outcome : Samples index) =>
    skorokhodGlobalRegularReconstructionCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2 (samples index outcome)
  let reconstruction := fun code outcome =>
    skorokhodGlobalRegularReconstructionCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2 ⟨sample outcome⟩
  have reconstructionsMeasurable (code index : ℕ) : Measurable (reconstructions code index) :=
    (skorokhodGlobalFiniteReconstruction_measurable_completion20261011 _).comp
      (measurable_pi_lambda _ fun coordinate => sampleEvaluations index _)
  have reconstructionMeasurable (code : ℕ) : Measurable (reconstruction code) :=
    (skorokhodGlobalFiniteReconstruction_measurable_completion20261011 _).comp
      (measurable_pi_lambda _ fun coordinate => evaluations _)
  apply probability_ae_sample_weak_of_reconstructions_completion20261011 laws law samples
    (fun outcome => (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space))
    samplesMeasurable (continuousGlobalFamily_measurable_completion20261011 sample sampleContinuous evaluations).aemeasurable
    reconstructions reconstruction (fun code index => (reconstructionsMeasurable code index).aemeasurable) (fun code => (reconstructionMeasurable code).aemeasurable)
  · intro code
    have reconstructed := skorokhodGlobal_reconstruction_weak_completion20261011
      (skorokhodGlobalRegularGridSelectionCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2)
      _ _ (finiteMarginals (Nat.unpair code).1 (Nat.unpair code).2)
    convert reconstructed using 1
    · funext index
      apply Subtype.ext
      change (laws index).map (reconstructions code index) =
        ((laws index).map (fun outcome => fun coordinate : Fin ((Nat.unpair code).2+2) =>
          samples index outcome (skorokhodGlobalRegularGridPointCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2 coordinate))).map
          (skorokhodGlobalFiniteReconstructionCompletion20261011
            (skorokhodGlobalRegularGridSelectionCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2))
      rw [Measure.map_map]
      · rfl
      · exact skorokhodGlobalFiniteReconstruction_measurable_completion20261011 _
      · exact measurable_pi_lambda _ fun coordinate => sampleEvaluations index _
    · apply congrArg (fun probability : ProbabilityMeasure (SkorokhodGlobalPathCompletion20261011 Space) => 𝓝 probability)
      apply Subtype.ext
      change law.map (reconstruction code) =
        (law.map (fun outcome => fun coordinate : Fin ((Nat.unpair code).2+2) =>
          sample outcome (skorokhodGlobalRegularGridPointCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2 coordinate))).map
          (skorokhodGlobalFiniteReconstructionCompletion20261011
            (skorokhodGlobalRegularGridSelectionCompletion20261011 (Nat.unpair code).1 (Nat.unpair code).2))
      rw [Measure.map_map]
      · rfl
      · exact skorokhodGlobalFiniteReconstruction_measurable_completion20261011 _
      · exact measurable_pi_lambda _ fun coordinate => evaluations _
  · intro tolerance error tolerancePositive errorPositive
    have tailConvergence : Tendsto (fun horizon : ℕ => 2 * (2 : ℝ)⁻¹ ^ (horizon+1)) atTop (𝓝 0) := by
      have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
      simpa only [pow_succ, mul_zero, zero_mul] using (geometric.mul_const (2 : ℝ)⁻¹).const_mul 2
    obtain ⟨horizon, tailSmall⟩ := (tailConvergence.eventually (gt_mem_nhds (by positivity : 0 < tolerance/2))).exists
    let localError := tolerance / (2 * (horizon+1 : ℝ))
    have localErrorPositive : 0 < localError := by dsimp [localError]; positivity
    obtain ⟨duration, durationPositive, sourceBound⟩ := modulus horizon localError error localErrorPositive errorPositive
    have physicalMesh : Tendsto (fun grid : ℕ => (horizon+1 : ℝ) / (grid+1 : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using skorokhodRegularGrid_mesh_tendsto_completion20261011.const_mul (horizon+1 : ℝ)
    have limitBound := (continuousGlobal_regular_grid_bad_probability_tendsto_completion20261011 law sample
      sampleContinuous evaluations horizon tolerance (tailSmall.trans (by linarith))).eventually (gt_mem_nhds errorPositive)
    obtain ⟨grid, mesh, limitProbability⟩ := ((physicalMesh.eventually (gt_mem_nhds durationPositive)).and limitBound).exists
    refine ⟨Nat.pair horizon grid, ?_, ?_⟩
    · filter_upwards [sourceBound] with index source
      obtain ⟨bad, badMeasurable, badProbability, good⟩ := source
      refine ⟨bad, badMeasurable, badProbability, ?_⟩
      intro outcome outside
      simp only [reconstructions, Nat.unpair_pair]
      have profileBound := fun coordinate before =>
        skorokhodGlobalRegularReconstruction_profile_bound_completion20261011 horizon grid (samples index outcome)
          duration localError localErrorPositive.le mesh (good outcome outside) coordinate (Nat.le_of_lt_succ before)
      have globalBound := skorokhodGlobal_dist_finite_profile_bound_completion20261011
        (samples index outcome) (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid (samples index outcome))
        (horizon+1) localError profileBound
      have identity : 2 * (horizon+1 : ℝ) * localError = tolerance := by dsimp [localError]; field_simp
      have castCount : ((horizon+1 : ℕ) : ℝ) = (horizon+1 : ℝ) := by norm_cast
      rw [castCount] at globalBound
      linarith
    · refine ⟨{outcome | tolerance < dist (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion20261011 Space)
        (skorokhodGlobalRegularReconstructionCompletion20261011 horizon grid ⟨sample outcome⟩)},
        measurableSet_lt measurable_const (continuousGlobal_grid_error_measurable_completion20261011 sample sampleContinuous evaluations horizon grid),
        limitProbability.le, ?_⟩
      intro outcome outside
      simp only [reconstruction, Nat.unpair_pair]
      exact le_of_not_gt outside

end
end IGSIII34.Diffusion

