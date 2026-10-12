import IGSIII34.Spectral.ActualDiagonalResolventCompletion
import IGSIII34.Spectral.ActualResolventPositivityCompletion
import IGSIII34.Diffusion.CoerciveObjectiveCompletion
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

local instance ActualContinuousObjectiveCompletionNorm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualContinuousObjectiveCompletionUniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualContinuousObjectiveCompletionTopology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualContinuousObjectiveCompletionInner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualContinuousObjectiveCompletionComplete :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
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
def actualContinuousForcingL2Completion
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    Lp ℝ 2 measure :=
  BoundedContinuousFunction.toLp 2 measure ℝ
    ((ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ) forcing)

theorem actualContinuousForcingL2_representative_completion
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualContinuousForcingL2Completion rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing =ᵐ[measure] forcing :=
  BoundedContinuousFunction.coeFn_toLp 2 measure ℝ ((ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ) forcing)

def actualContinuousForcingDualCompletion
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    StrongDual ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (innerSL ℝ (actualContinuousForcingL2Completion rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing)).comp
    (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

theorem actualContinuousForcingDual_integral_completion
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualContinuousForcingDualCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing potential =
      ∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ∂measure := by
  change inner ℝ (actualContinuousForcingL2Completion rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing)
    (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [actualContinuousForcingL2_representative_completion rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing,
    actualEnergyL2Embedding_representative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential]
    with point forcingEquality potentialEquality
  rw [forcingEquality, potentialEquality]
  change actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point * forcing point = _
  ring

/-- The quadratic coercive objective is exactly the original limit energy,
mass and forcing functional on the actual carrier. -/
theorem actualContinuousObjective_integral_completion
    (parameter : ℝ)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    coerciveObjectiveCompletion
      (parameterAnchoredResolventBilinearCompletion
        (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) parameter)
      (actualContinuousForcingDualCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing) potential =
      parameter * (∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 ∂measure) +
        limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val -
        2 * (∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ∂measure) := by
  rw [coerciveObjectiveCompletion, actualParameterResolventBilinear_self_completion,
    actualContinuousForcingDual_integral_completion]
  ring

variable [measure.IsOpenPosMeasure]

def actualContinuousEnergySolutionCompletion (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  parameterEnergySolutionCompletion
    (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne (actualContinuousForcingL2Completion rule p positive belowOne fixedPoint growth value growthPositive marks measure forcing)

theorem actualContinuousEnergySolution_variational_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (test : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    parameterAnchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) parameter
      (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) test =
      actualContinuousForcingDualCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing test :=
  parameterEnergySolution_variational_completion _ _ _ _ _ _ _

end
end IGSIII34.Diffusion
