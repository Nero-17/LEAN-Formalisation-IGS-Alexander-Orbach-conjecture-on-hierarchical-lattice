import IGSIII34.Diffusion.DiscreteIntervalSkorokhodSampleCompletion
import IGSIII34.Diffusion.ContinuousSkorokhodGridApproximationCompletion
import IGSIII34.Diffusion.FlooredIntervalModulusCompletion
import IGSIII34.Diffusion.PathWeakReconstructionCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space Outcome : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Outcome]

local instance discreteSkorokhodContinuousPathMeasurableCompletion :
    MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
local instance discreteSkorokhodContinuousPathBorelCompletion :
    BorelSpace C(SkorokhodIntervalTimeCompletion, Space) := ⟨rfl⟩

/-- True accelerated finite-walk laws converge in the actual J1 path
topology once their finite grid laws and the proved real chain modulus
estimates are supplied. The limit sample is continuous-valued, and its
reconstruction errors are proved by uniform continuity and dominated
convergence inside this theorem. -/
theorem discreteSkorokhod_weak_of_finite_marginals_and_chain_modulus_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth)) (scales : ℕ → ℝ) (scaleNonnegative : ∀ depth, 0 ≤ scales depth)
    (horizon : ℝ≥0) (placement : ∀ depth, Vertices depth → Space)
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → C(SkorokhodIntervalTimeCompletion, Space)) (sampleMeasurable : Measurable sample)
    (finiteMarginals : ∀ grid,
      Tendsto (fun depth => (discreteWalkProbabilityCompletion (endpoint depth) (positiveDegree depth) (initial depth)).map
        (show AEMeasurable (fun path : ℕ → Vertices depth => fun index : Fin (grid + 2) =>
          placement depth (path ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion grid index : ℝ)⌋₊)) _ from
          (measurable_pi_lambda _ fun index => (measurable_of_finite (placement depth)).comp (measurable_pi_apply ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion grid index : ℝ)⌋₊)).aemeasurable)) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
          (show AEMeasurable (fun outcome => fun index : Fin (grid + 2) =>
            sample outcome (skorokhodRegularGridPointCompletion grid index)) law from
            (measurable_pi_lambda _ fun index => (continuous_eval_const _).measurable.comp sampleMeasurable).aemeasurable))))
    (chainModulus : ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion (placement depth) (scales depth) horizon duration tolerance) ≤ error) :
    Tendsto (fun depth => discreteIntervalSkorokhodProbabilityCompletion (endpoint depth) (positiveDegree depth)
      (initial depth) (scales depth) (scaleNonnegative depth) horizon (placement depth)) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
        (continuousIntervalPath_lipschitz_completion.continuous.measurable.comp sampleMeasurable).aemeasurable)) := by
  let laws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  let samples := fun depth => discreteIntervalSkorokhodSampleCompletion (scales depth) horizon (placement depth)
  let reconstructions := fun grid depth (path : ℕ → Vertices depth) =>
    skorokhodFiniteReconstructionCompletion (skorokhodRegularGridSelectionCompletion grid)
      (fun index => placement depth (path ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion grid index : ℝ)⌋₊))
  let reconstruction := fun grid outcome => continuousSkorokhodRegularReconstructionCompletion grid (sample outcome)
  have reconstructionMeasurable (grid : ℕ) : Measurable (reconstruction grid) :=
    (continuousSkorokhodRegularReconstruction_continuous_completion grid).measurable.comp sampleMeasurable
  have reconstructionsMeasurable (grid depth : ℕ) : Measurable (reconstructions grid depth) :=
    skorokhod_reconstructed_sample_measurable_completion _ _
      (measurable_pi_lambda _ fun index => (measurable_of_finite (placement depth)).comp (measurable_pi_apply _))
  apply probability_sample_weak_of_reconstructions_completion laws law samples
    (fun outcome => continuousIntervalPathCompletion (sample outcome))
    (fun depth => discreteIntervalSkorokhodSample_measurable_completion _ (scaleNonnegative depth) horizon _)
    (continuousIntervalPath_lipschitz_completion.continuous.measurable.comp sampleMeasurable)
    reconstructions reconstruction reconstructionsMeasurable reconstructionMeasurable
  · intro grid
    have reconstructed := skorokhod_reconstruction_weak_convergence_completion
      (skorokhodRegularGridSelectionCompletion grid) _ _ (finiteMarginals grid)
    convert reconstructed using 1
    · funext depth
      apply Subtype.ext
      change (laws depth).map (reconstructions grid depth) =
        ((laws depth).map (fun path : ℕ → Vertices depth => fun index : Fin (grid + 2) =>
          placement depth (path ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion grid index : ℝ)⌋₊))).map
          (skorokhodFiniteReconstructionCompletion (skorokhodRegularGridSelectionCompletion grid))
      rw [Measure.map_map]
      · rfl
      · exact skorokhodFiniteReconstruction_measurable_completion _
      · exact measurable_pi_lambda _ fun index => (measurable_of_finite (placement _)).comp (measurable_pi_apply _)
    · apply congrArg (fun probability : ProbabilityMeasure (SkorokhodIntervalPathCompletion Space) => 𝓝 probability)
      apply Subtype.ext
      change law.map (reconstruction grid) =
        (law.map (fun outcome => fun index : Fin (grid + 2) => sample outcome (skorokhodRegularGridPointCompletion grid index))).map
          (skorokhodFiniteReconstructionCompletion (skorokhodRegularGridSelectionCompletion grid))
      rw [Measure.map_map]
      · rfl
      · exact skorokhodFiniteReconstruction_measurable_completion _
      · exact measurable_pi_lambda _ fun index => (continuous_eval_const _).measurable.comp sampleMeasurable
  · intro tolerance error tolerancePositive errorPositive
    obtain ⟨duration, durationPositive, chainBound⟩ := chainModulus tolerance error tolerancePositive errorPositive
    have physicalMesh : Tendsto (fun grid : ℕ => (horizon : ℝ) * (1 / (grid + 1 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using skorokhodRegularGrid_mesh_tendsto_completion.const_mul (horizon : ℝ)
    have limitBound := (continuousSkorokhodRegular_bad_probability_tendsto_completion law sample sampleMeasurable
      tolerance tolerancePositive).eventually (gt_mem_nhds errorPositive)
    obtain ⟨grid, mesh, limitProbability⟩ := ((physicalMesh.eventually (gt_mem_nhds durationPositive)).and limitBound).exists
    refine ⟨grid, ?_, ?_⟩
    · filter_upwards [chainBound] with depth bound
      refine ⟨finiteIntervalChainBadModulusCompletion (placement depth) (scales depth) horizon duration tolerance,
        finiteIntervalChainBadModulus_measurable_completion _ (measurable_of_finite _) _ _ _ _, bound, ?_⟩
      intro path good
      apply (edist_le_ofReal tolerancePositive.le).mp
      apply skorokhod_reconstruction_modulus_bound_completion
        (skorokhodRegularGridPointCompletion grid) (skorokhodRegularGridSelectionCompletion grid)
        (samples depth path) (1 / (grid + 1 : ℝ)) tolerance
        (skorokhodRegularGridSelection_near_completion grid)
      intro first second close
      apply finiteIntervalChain_good_modulus_completion _ _ _ _ _ (scaleNonnegative depth) horizon.property path good first second
      exact (mul_le_mul_of_nonneg_left close.le horizon.property).trans_lt mesh
    · refine ⟨{outcome | tolerance < dist (continuousIntervalPathCompletion (sample outcome)) (reconstruction grid outcome)},
        measurableSet_lt measurable_const ((continuousSkorokhodRegular_error_continuous_completion grid).measurable.comp sampleMeasurable),
        limitProbability.le, ?_⟩
      intro outcome good
      exact le_of_not_gt good

end
end IGSIII34.Diffusion


