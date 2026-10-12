import IGSIII34.Spectral.ActualResolventCompletion
import IGSIII34.Diffusion.NormalizedUniformResolventCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms IGSIII34.Spectral
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace
open scoped Topology BoundedContinuousFunction

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualNormalizedNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualNormalizedUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualNormalizedTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualNormalizedInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualNormalizedCompleteCompletion :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

theorem actualAnchoredEnergySquare_eq_limitingEnergy_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    anchoredEnergySquareCompletion
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) potential =
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val := by
  rw [anchoredEnergySquareCompletion,
    actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential,
    actualAnchorEvaluation_apply_completion]
  ring

theorem actualAnchoredEnergySquare_nonnegative_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    0 ≤ anchoredEnergySquareCompletion
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) potential := by
  rw [actualAnchoredEnergySquare_eq_limitingEnergy_completion]
  exact limitingEnergy_nonnegative _ _
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) potential.property

def actualNormalizedResolventSolutionCompletion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  normalizedAnchoredResolventSolutionCompletion
    (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne forcing

/-- The true electrical finite-energy resolvent approximates every
finite-energy cutoff uniformly on the actual completed carrier. -/
theorem actualNormalizedResolventSolution_uniform_tendsto_completion [measure.IsOpenPosMeasure]
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop)
    (forcing : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    Tendsto (fun index => actualEnergyBoundedEmbeddingCompletion rule p positive belowOne fixedPoint
      growth value growthPositive marks anchor
      (actualNormalizedResolventSolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive
        marks anchor measure (parameters index) (parametersAtLeastOne index) forcing)) atTop
      (𝓝 (actualEnergyBoundedEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor forcing)) :=
  normalizedAnchoredResolventSolution_uniform_tendsto_completion measure
    (actualEnergyBoundedEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualEnergyBoundedEmbedding_compact_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchoredEnergySquare_nonnegative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    parameters parametersAtLeastOne parametersDiverge forcing

end
end IGSIII34.Diffusion
