import IGSIII34.Diffusion.DiscreteIntervalSkorokhodSampleCompletion20261011
import IGSIII34.Diffusion.ContinuousSkorokhodGridApproximationCompletion20261011
import IGSIII34.Diffusion.FlooredIntervalModulusCompletion20261011
import IGSIII34.Diffusion.PathWeakReconstructionCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

variable {Space Outcome : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Outcome]

local instance discreteSkorokhodContinuousPathMeasurableCompletion20261011 :
    MeasurableSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := borel _
local instance discreteSkorokhodContinuousPathBorelCompletion20261011 :
    BorelSpace C(SkorokhodIntervalTimeCompletion20261011, Space) := ⟨rfl⟩

/-- True accelerated finite-walk laws converge in the actual J1 path
topology once their finite grid laws and the proved real chain modulus
estimates are supplied. The limit sample is continuous-valued, and its
reconstruction errors are proved by uniform continuity and dominated
convergence inside this theorem. -/
theorem discreteSkorokhod_weak_of_finite_marginals_and_chain_modulus_completion20261011
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth)) (scales : ℕ → ℝ) (scaleNonnegative : ∀ depth, 0 ≤ scales depth)
    (horizon : ℝ≥0) (placement : ∀ depth, Vertices depth → Space)
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample : Outcome → C(SkorokhodIntervalTimeCompletion20261011, Space)) (sampleMeasurable : Measurable sample)
    (finiteMarginals : ∀ grid,
      Tendsto (fun depth => (discreteWalkProbabilityCompletion20261011 (endpoint depth) (positiveDegree depth) (initial depth)).map
        (show AEMeasurable (fun path : ℕ → Vertices depth => fun index : Fin (grid + 2) =>
          placement depth (path ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion20261011 grid index : ℝ)⌋₊)) _ from
          (measurable_pi_lambda _ fun index => (measurable_of_finite (placement depth)).comp (measurable_pi_apply ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion20261011 grid index : ℝ)⌋₊)).aemeasurable)) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
          (show AEMeasurable (fun outcome => fun index : Fin (grid + 2) =>
            sample outcome (skorokhodRegularGridPointCompletion20261011 grid index)) law from
            (measurable_pi_lambda _ fun index => (continuous_eval_const _).measurable.comp sampleMeasurable).aemeasurable))))
    (chainModulus : ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)).real
          (finiteIntervalChainBadModulusCompletion20261011 (placement depth) (scales depth) horizon duration tolerance) ≤ error) :
    Tendsto (fun depth => discreteIntervalSkorokhodProbabilityCompletion20261011 (endpoint depth) (positiveDegree depth)
      (initial depth) (scales depth) (scaleNonnegative depth) horizon (placement depth)) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
        (continuousIntervalPath_lipschitz_completion20261011.continuous.measurable.comp sampleMeasurable).aemeasurable)) := by
  let laws := fun depth => finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  let samples := fun depth => discreteIntervalSkorokhodSampleCompletion20261011 (scales depth) horizon (placement depth)
  let reconstructions := fun grid depth (path : ℕ → Vertices depth) =>
    skorokhodFiniteReconstructionCompletion20261011 (skorokhodRegularGridSelectionCompletion20261011 grid)
      (fun index => placement depth (path ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion20261011 grid index : ℝ)⌋₊))
  let reconstruction := fun grid outcome => continuousSkorokhodRegularReconstructionCompletion20261011 grid (sample outcome)
  have reconstructionMeasurable (grid : ℕ) : Measurable (reconstruction grid) :=
    (continuousSkorokhodRegularReconstruction_continuous_completion20261011 grid).measurable.comp sampleMeasurable
  have reconstructionsMeasurable (grid depth : ℕ) : Measurable (reconstructions grid depth) :=
    skorokhod_reconstructed_sample_measurable_completion20261011 _ _
      (measurable_pi_lambda _ fun index => (measurable_of_finite (placement depth)).comp (measurable_pi_apply _))
  apply probability_sample_weak_of_reconstructions_completion20261011 laws law samples
    (fun outcome => continuousIntervalPathCompletion20261011 (sample outcome))
    (fun depth => discreteIntervalSkorokhodSample_measurable_completion20261011 _ (scaleNonnegative depth) horizon _)
    (continuousIntervalPath_lipschitz_completion20261011.continuous.measurable.comp sampleMeasurable)
    reconstructions reconstruction reconstructionsMeasurable reconstructionMeasurable
  · intro grid
    have reconstructed := skorokhod_reconstruction_weak_convergence_completion20261011
      (skorokhodRegularGridSelectionCompletion20261011 grid) _ _ (finiteMarginals grid)
    convert reconstructed using 1
    · funext depth
      apply Subtype.ext
      change (laws depth).map (reconstructions grid depth) =
        ((laws depth).map (fun path : ℕ → Vertices depth => fun index : Fin (grid + 2) =>
          placement depth (path ⌊scales depth * (horizon : ℝ) * (skorokhodRegularGridPointCompletion20261011 grid index : ℝ)⌋₊))).map
          (skorokhodFiniteReconstructionCompletion20261011 (skorokhodRegularGridSelectionCompletion20261011 grid))
      rw [Measure.map_map]
      · rfl
      · exact skorokhodFiniteReconstruction_measurable_completion20261011 _
      · exact measurable_pi_lambda _ fun index => (measurable_of_finite (placement _)).comp (measurable_pi_apply _)
    · apply congrArg (fun probability : ProbabilityMeasure (SkorokhodIntervalPathCompletion20261011 Space) => 𝓝 probability)
      apply Subtype.ext
      change law.map (reconstruction grid) =
        (law.map (fun outcome => fun index : Fin (grid + 2) => sample outcome (skorokhodRegularGridPointCompletion20261011 grid index))).map
          (skorokhodFiniteReconstructionCompletion20261011 (skorokhodRegularGridSelectionCompletion20261011 grid))
      rw [Measure.map_map]
      · rfl
      · exact skorokhodFiniteReconstruction_measurable_completion20261011 _
      · exact measurable_pi_lambda _ fun index => (continuous_eval_const _).measurable.comp sampleMeasurable
  · intro tolerance error tolerancePositive errorPositive
    obtain ⟨duration, durationPositive, chainBound⟩ := chainModulus tolerance error tolerancePositive errorPositive
    have physicalMesh : Tendsto (fun grid : ℕ => (horizon : ℝ) * (1 / (grid + 1 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using skorokhodRegularGrid_mesh_tendsto_completion20261011.const_mul (horizon : ℝ)
    have limitBound := (continuousSkorokhodRegular_bad_probability_tendsto_completion20261011 law sample sampleMeasurable
      tolerance tolerancePositive).eventually (gt_mem_nhds errorPositive)
    obtain ⟨grid, mesh, limitProbability⟩ := ((physicalMesh.eventually (gt_mem_nhds durationPositive)).and limitBound).exists
    refine ⟨grid, ?_, ?_⟩
    · filter_upwards [chainBound] with depth bound
      refine ⟨finiteIntervalChainBadModulusCompletion20261011 (placement depth) (scales depth) horizon duration tolerance,
        finiteIntervalChainBadModulus_measurable_completion20261011 _ (measurable_of_finite _) _ _ _ _, bound, ?_⟩
      intro path good
      apply (edist_le_ofReal tolerancePositive.le).mp
      apply skorokhod_reconstruction_modulus_bound_completion20261011
        (skorokhodRegularGridPointCompletion20261011 grid) (skorokhodRegularGridSelectionCompletion20261011 grid)
        (samples depth path) (1 / (grid + 1 : ℝ)) tolerance
        (skorokhodRegularGridSelection_near_completion20261011 grid)
      intro first second close
      apply finiteIntervalChain_good_modulus_completion20261011 _ _ _ _ _ (scaleNonnegative depth) horizon.property path good first second
      exact (mul_le_mul_of_nonneg_left close.le horizon.property).trans_lt mesh
    · refine ⟨{outcome | tolerance < dist (continuousIntervalPathCompletion20261011 (sample outcome)) (reconstruction grid outcome)},
        measurableSet_lt measurable_const ((continuousSkorokhodRegular_error_continuous_completion20261011 grid).measurable.comp sampleMeasurable),
        limitProbability.le, ?_⟩
      intro outcome good
      exact le_of_not_gt good

end
end IGSIII34.Diffusion


