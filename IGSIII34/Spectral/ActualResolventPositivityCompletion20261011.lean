import IGSIII34.Spectral.ActualResolventCompletion20261011
import IGSIII34.Spectral.ParameterFormSpectrumCompletion20261011
import IGSIII34.ResistanceLimit.TruncationPairingCompletion20261011

/-! Positivity of the actual Lax-Milgram resolvent, obtained from the negative
part energy test. No Markov or positivity property is supplied as an input. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology BoundedContinuousFunction
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance ActualResolventPositivityCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualResolventPositivityCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualResolventPositivityCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualResolventPositivityCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualResolventPositivityCompletion20261011Complete :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

theorem actualEnergyL2Embedding_representative_completion20261011
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential =ᵐ[measure]
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential :=
  BoundedContinuousFunction.coeFn_toLp 2 measure ℝ
    (actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential)

theorem actualAnchoredInner_energy_pairing_completion20261011
    (first second : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    inner ℝ first second =
      limitingPairing (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) first.val second.val +
      first.val anchor * second.val anchor := rfl

def actualEnergyNegativePartCompletion20261011
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  ⟨fun point => min (potential.val point) 0,
    energyDomain_normal_contraction
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
      (fun scalar => min scalar 0) negative_part_contracts_completion20261011 potential.property⟩

theorem actualEnergyNegativePart_extension_completion20261011
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualEnergyNegativePartCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential) point =
    min (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point) 0 :=
  completionExtension_contraction_completion20261011
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
    (fun scalar => min scalar 0) (continuous_id.min continuous_const) negative_part_contracts_completion20261011 potential point

theorem actual_parameter_resolvent_nonnegative_completion20261011 [measure.IsOpenPosMeasure]
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Lp ℝ 2 measure)
    (forcingNonnegative : ∀ᵐ point ∂measure, 0 ≤ forcing point)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    0 ≤ actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (parameterEnergySolutionCompletion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
        (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        parameter parameterAtLeastOne forcing) point := by
  let solution := parameterEnergySolutionCompletion20261011
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne forcing
  let negative := actualEnergyNegativePartCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor solution
  let embedding := actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
  have solutionRepresentative := actualEnergyL2Embedding_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure solution
  have negativeRepresentative := actualEnergyL2Embedding_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure negative
  have negativeExtension (vertex : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks negative vertex =
      min (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks solution vertex) 0 :=
    actualEnergyNegativePart_extension_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor solution vertex
  have forcingPairingNonpositive : inner ℝ forcing (embedding negative) ≤ 0 := by
    rw [L2.inner_def]
    apply integral_nonpos_of_ae
    filter_upwards [forcingNonnegative, negativeRepresentative] with vertex nonnegative representative
    rw [representative, negativeExtension]
    simp only [Real.inner_apply, Pi.zero_apply]
    change forcing vertex * min (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks solution vertex) 0 ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos nonnegative (min_le_right _ _)
  have negativeL2Identity : inner ℝ (embedding solution) (embedding negative) = ‖embedding negative‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [solutionRepresentative, negativeRepresentative] with vertex solutionAt negativeAt
    rw [solutionAt, negativeAt, negativeExtension]
    simp only [Real.inner_apply]
    change _ * min _ 0 = min _ 0 * min _ 0
    by_cases nonpositive : actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks solution vertex ≤ 0
    · rw [min_eq_left nonpositive]
    · rw [min_eq_right (le_of_not_ge nonpositive)]; simp
  have energyPairingNonnegative : 0 ≤ limitingPairing
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) solution.val negative.val := by
    exact (limitingEnergy_nonnegative _ _
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) negative.property).trans
      (limitingEnergy_negative_part_le_pairing_completion20261011 _ _
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks) solution)
  have variational := parameterEnergySolution_variational_completion20261011 embedding
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne forcing negative
  rw [parameterAnchoredResolventBilinear_apply_completion20261011,
    actualAnchoredInner_energy_pairing_completion20261011,
    actualAnchorEvaluation_apply_completion20261011,
    actualAnchorEvaluation_apply_completion20261011, negativeL2Identity] at variational
  have negativeNormZero : ‖embedding negative‖ = 0 := by
    nlinarith [sq_nonneg ‖embedding negative‖, norm_nonneg (embedding negative)]
  have negativeZero : negative = 0 := by
    apply actualEnergyL2Embedding_injective_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    simpa only [map_zero] using norm_eq_zero.mp negativeNormZero
  have negativeAtZero := congrArg (fun potential => actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point) negativeZero
  rw [negativeExtension, map_zero, ContinuousMap.zero_apply] at negativeAtZero
  change 0 ≤ actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks solution point
  by_contra notNonnegative
  rw [min_eq_left (le_of_lt (lt_of_not_ge notNonnegative))] at negativeAtZero
  linarith

end
end IGSIII34.Spectral



