import IGSIII34.Spectral.ActualDiagonalResolventCompletion20261011
import IGSIII34.Spectral.ActualResolventPositivityCompletion20261011
import IGSIII34.Diffusion.CoerciveObjectiveCompletion20261011
import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Spectral
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

local instance ActualContinuousObjectiveCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualContinuousObjectiveCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualContinuousObjectiveCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualContinuousObjectiveCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualContinuousObjectiveCompletion20261011Complete :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

/-- Canonical L² forcing associated with a continuous function on the
actual compact electrical carrier. -/
def actualContinuousForcingL2Completion20261011
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    Lp ℝ 2 measure :=
  BoundedContinuousFunction.toLp 2 measure ℝ
    ((ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ) forcing)

theorem actualContinuousForcingL2_representative_completion20261011
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualContinuousForcingL2Completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing =ᵐ[measure] forcing :=
  BoundedContinuousFunction.coeFn_toLp 2 measure ℝ ((ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ) forcing)

def actualContinuousForcingDualCompletion20261011
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    StrongDual ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (innerSL ℝ (actualContinuousForcingL2Completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing)).comp
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

theorem actualContinuousForcingDual_integral_completion20261011
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualContinuousForcingDualCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing potential =
      ∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ∂measure := by
  change inner ℝ (actualContinuousForcingL2Completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing)
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualContinuousForcingL2_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing,
    actualEnergyL2Embedding_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential]
    with point forcingEquality potentialEquality
  rw [forcingEquality, potentialEquality]
  change actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point * forcing point = _
  ring

/-- The quadratic coercive objective is exactly the original limit energy,
mass and forcing functional on the actual carrier. -/
theorem actualContinuousObjective_integral_completion20261011
    (parameter : ℝ)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    coerciveObjectiveCompletion20261011
      (parameterAnchoredResolventBilinearCompletion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) parameter)
      (actualContinuousForcingDualCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing) potential =
      parameter * (∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 ∂measure) +
        limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val -
        2 * (∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ∂measure) := by
  rw [coerciveObjectiveCompletion20261011, actualParameterResolventBilinear_self_completion20261011,
    actualContinuousForcingDual_integral_completion20261011]
  ring

variable [measure.IsOpenPosMeasure]

def actualContinuousEnergySolutionCompletion20261011 (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  parameterEnergySolutionCompletion20261011
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne (actualContinuousForcingL2Completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing)

theorem actualContinuousEnergySolution_variational_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (test : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    parameterAnchoredResolventBilinearCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) parameter
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) test =
      actualContinuousForcingDualCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing test :=
  parameterEnergySolution_variational_completion20261011 _ _ _ _ _ _ _

end
end IGSIII34.Diffusion
