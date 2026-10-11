import IGSIII34.Spectral.ActualResolventCompletion20261011
import IGSIII34.Diffusion.NormalizedUniformResolventCompletion20261011

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

local instance actualNormalizedNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualNormalizedUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualNormalizedTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualNormalizedInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualNormalizedCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

theorem actualAnchoredEnergySquare_eq_limitingEnergy_completion20261011
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    anchoredEnergySquareCompletion20261011
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) potential =
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val := by
  rw [anchoredEnergySquareCompletion20261011,
    actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential,
    actualAnchorEvaluation_apply_completion20261011]
  ring

theorem actualAnchoredEnergySquare_nonnegative_completion20261011
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    0 ≤ anchoredEnergySquareCompletion20261011
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) potential := by
  rw [actualAnchoredEnergySquare_eq_limitingEnergy_completion20261011]
  exact limitingEnergy_nonnegative _ _
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) potential.property

def actualNormalizedResolventSolutionCompletion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  normalizedAnchoredResolventSolutionCompletion20261011
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne forcing

/-- The true electrical finite-energy resolvent approximates every
finite-energy cutoff uniformly on the actual completed carrier. -/
theorem actualNormalizedResolventSolution_uniform_tendsto_completion20261011 [measure.IsOpenPosMeasure]
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop)
    (forcing : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    Tendsto (fun index => actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks anchor
      (actualNormalizedResolventSolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive
        marks anchor measure (parameters index) (parametersAtLeastOne index) forcing)) atTop
      (𝓝 (actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor forcing)) :=
  normalizedAnchoredResolventSolution_uniform_tendsto_completion20261011 measure
    (actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualEnergyBoundedEmbedding_compact_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchoredEnergySquare_nonnegative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    parameters parametersAtLeastOne parametersDiverge forcing

end
end IGSIII34.Diffusion
