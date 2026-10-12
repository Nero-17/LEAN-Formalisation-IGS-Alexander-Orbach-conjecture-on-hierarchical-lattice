import IGSIII34.Diffusion.NormalizedAnchoredResolventCompletion
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Spectral InnerProductSpace MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

/-- A proved compact continuous embedding upgrades the actual variational
resolvent approximation to uniform approximation of each finite-energy
potential. This does not assume a Feller semigroup or any process limit. -/
theorem normalizedAnchoredResolventSolution_uniform_tendsto_completion
    {Energy Carrier : Type*}
    [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    [TopologicalSpace Carrier] [MeasurableSpace Carrier] [BorelSpace Carrier]
    (measure : Measure Carrier) [IsFiniteMeasure measure] [measure.IsOpenPosMeasure]
    (continuousEmbedding : Energy →L[ℝ] (Carrier →ᵇ ℝ))
    (compactEmbedding : IsCompactOperator continuousEmbedding)
    (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion
      ((BoundedContinuousFunction.toLp 2 measure ℝ).comp continuousEmbedding) anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion anchorEvaluation potential)
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop) (forcing : Energy) :
    Tendsto (fun index => continuousEmbedding (normalizedAnchoredResolventSolutionCompletion
      (Energy := Energy) (L2 := Lp ℝ 2 measure)
      ((BoundedContinuousFunction.toLp 2 measure ℝ).comp continuousEmbedding) anchorEvaluation baseCoercive
      (parameters index) (parametersAtLeastOne index) forcing)) atTop (𝓝 (continuousEmbedding forcing)) := by
  let L2Embedding := (BoundedContinuousFunction.toLp 2 measure ℝ).comp continuousEmbedding
  obtain ⟨bound, boundNonnegative, forcingBound, solutionBound⟩ :=
    normalizedAnchoredResolventSolution_domain_bound_completion L2Embedding anchorEvaluation
      baseCoercive energyNonnegative forcing
  let family := closure (continuousEmbedding '' Metric.closedBall 0 bound)
  have familyCompact : IsCompact family := compactEmbedding.isCompact_closure_image_closedBall bound
  have forcingMember : continuousEmbedding forcing ∈ family :=
    subset_closure ⟨forcing, by simpa only [Metric.mem_closedBall, dist_zero_right] using forcingBound, rfl⟩
  have solutionMember (index : ℕ) : continuousEmbedding
      (normalizedAnchoredResolventSolutionCompletion L2Embedding anchorEvaluation
        baseCoercive (parameters index) (parametersAtLeastOne index) forcing) ∈ family := by
    apply subset_closure
    refine ⟨_, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (solutionBound (parameters index) (parametersAtLeastOne index))
  let potentials : ℕ → family := fun index => ⟨_, solutionMember index⟩
  let limit : family := ⟨continuousEmbedding forcing, forcingMember⟩
  have L2Converges := normalizedAnchoredResolventSolution_L2_tendsto_completion L2Embedding
    anchorEvaluation baseCoercive energyNonnegative parameters parametersAtLeastOne parametersDiverge forcing
  have convertedConverges : Tendsto
      (fun index => BoundedContinuousFunction.toLp 2 measure ℝ (potentials index).val) atTop
      (𝓝 (BoundedContinuousFunction.toLp 2 measure ℝ limit.val)) := L2Converges
  have uniform := compact_family_L2_to_uniform_completion measure family familyCompact potentials limit atTop
    convertedConverges
  exact uniform

end
end IGSIII34.Diffusion
