import IGSIII34.Spectral.ActualDiagonalResolventCompletion20261011
import IGSIII34.Spectral.ParameterEvaluationBoundsCompletion20261011
import IGSIII34.Spectral.ActualCutoffQuotientCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

def actualDiagonalVariationalResolventCompletion20261011 (parameter : ℝ)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) : ℝ :=
  sSup (Set.range (fun potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks =>
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
      (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
        parameter * ∫ other, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2 ∂measure)))

variable (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)

local instance : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance : UniformSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance : CompleteSpace
    (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [measure.IsOpenPosMeasure]

include anchor in
theorem actual_completion_quotient_range_bddAbove_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    BddAbove (Set.range (fun potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks =>
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
        (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
          parameter * ∫ other, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2 ∂measure))) := by
  have bounded := parameterFormEvaluation_quotient_bddAbove_completion20261011
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne
    (continuousFormEvaluationCompletion20261011
      (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) point)
  obtain ⟨bound, bounded⟩ := bounded
  refine ⟨bound, ?_⟩
  rintro result ⟨potential, rfl⟩
  let anchoredPotential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor := potential
  have estimate := bounded ⟨anchoredPotential, rfl⟩
  dsimp only at estimate
  rw [actualParameterResolventBilinear_self_completion20261011,
    actualContinuousFormEvaluation_apply_completion20261011] at estimate
  exact estimate

include anchor in
theorem actual_completion_quotient_le_diagonal_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
      (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
        parameter * ∫ other, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2 ∂measure) ≤
      actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point := by
  exact le_csSup (actual_completion_quotient_range_bddAbove_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks measure anchor parameter parameterAtLeastOne point) ⟨potential, rfl⟩

include anchor in
theorem actual_completion_diagonal_cutoff_lower_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (atPoint : actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point = 1)
    (energyBound massBound : ℝ)
    (energyEstimate : limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val ≤ energyBound)
    (massEstimate : (∫ other,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2 ∂measure) ≤ massBound) :
    1 / (energyBound + parameter * massBound) ≤
      actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point :=
  (actual_completion_cutoff_quotient_lower_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure
    potential point atPoint energyBound massBound energyEstimate massEstimate parameter (zero_lt_one.trans_le parameterAtLeastOne)).trans
    (actual_completion_quotient_le_diagonal_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure
      anchor parameter parameterAtLeastOne point potential)

theorem actual_completion_diagonal_local_upper_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (cell : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    (cellMeasurable : MeasurableSet cell) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ other ∈ cell, dist point other ≤ diameter)
    (massPositive : 0 < measure.real cell) :
    actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point ≤
      2 * max (1 / (parameter * measure.real cell)) diameter := by
  apply csSup_le (Set.range_nonempty _)
  rintro result ⟨potential, rfl⟩
  exact actual_local_completion_resolvent_evaluation_bound_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks measure point cell cellMeasurable diameter diameterNonnegative diameterBound massPositive
    parameter (zero_lt_one.trans_le parameterAtLeastOne) potential

end
end IGSIII34.Spectral
