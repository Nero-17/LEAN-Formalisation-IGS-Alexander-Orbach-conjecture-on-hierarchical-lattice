import IGSIII34.Spectral.ActualResolventConservationCompletion20261011
import Mathlib.MeasureTheory.Function.LpOrder

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

local instance ActualResolventMarkovCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualResolventMarkovCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualResolventMarkovCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualResolventMarkovCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualResolventMarkovCompletion20261011Complete :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

def actualParameterL2ResolventCompletion20261011 (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure :=
  (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).comp
    (parameterEnergySolutionCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      parameter parameterAtLeastOne)

theorem actualParameterL2Resolvent_positive_completion20261011 [measure.IsOpenPosMeasure]
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Lp ℝ 2 measure) (nonnegative : 0 ≤ forcing) :
    0 ≤ actualParameterL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne forcing := by
  apply (Lp.coeFn_nonneg _).mp
  have representative := actualEnergyL2Embedding_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (parameterEnergySolutionCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      parameter parameterAtLeastOne forcing)
  filter_upwards [representative] with point equality
  simp only [actualParameterL2ResolventCompletion20261011, ContinuousLinearMap.comp_apply, Pi.zero_apply]
  rw [equality]
  exact actual_parameter_resolvent_nonnegative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    parameter parameterAtLeastOne forcing ((Lp.coeFn_nonneg _).mpr nonnegative) point

theorem actual_normalized_parameter_resolvent_positive_completion20261011 [measure.IsOpenPosMeasure]
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Lp ℝ 2 measure) (nonnegative : 0 ≤ forcing) :
    0 ≤ (parameter • actualParameterL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne) forcing := by
  have imageNonnegative := (Lp.coeFn_nonneg _).mpr
    (actualParameterL2Resolvent_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne forcing nonnegative)
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [Lp.coeFn_smul parameter
    (actualParameterL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure parameter parameterAtLeastOne forcing),
    imageNonnegative] with point scalar nonnegativeAt
  simp only [ContinuousLinearMap.smul_apply, Pi.zero_apply]
  rw [scalar, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (by linarith) nonnegativeAt

theorem actual_normalized_parameter_resolvent_constant_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (constant : ℝ) :
    (parameter • actualParameterL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne)
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)) =
    actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
  rw [ContinuousLinearMap.smul_apply, ← map_smul]
  change actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (parameterEnergySolutionCompletion20261011 _ _ _ parameter parameterAtLeastOne
      (parameter • actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant))) = _
  rw [actual_parameter_resolvent_constant_completion20261011]

end
end IGSIII34.Spectral


