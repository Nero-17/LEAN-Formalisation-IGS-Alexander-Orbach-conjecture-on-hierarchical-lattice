import IGSIII34.Spectral.ActualTransitionKernelCompletion20261011
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory ProbabilityTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology BoundedContinuousFunction NNReal ProbabilityTheory
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualTransitionContinuousNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualTransitionContinuousUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualTransitionContinuousTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualTransitionContinuousInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualTransitionContinuousCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

variable [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualTransitionProbability_joint_continuous_completion20261011 :
    Continuous (fun pair : ℝ≥0 × UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) =>
        actualTransitionProbabilityCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data pair.1 pair.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro function
  have same : (fun pair : ℝ≥0 × UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) =>
      ∫ other, function other ∂actualTransitionProbabilityCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data pair.1 pair.2) =
    (fun pair => actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative pair.1 function pair.2) := by
    funext pair
    exact actualTransitionKernel_continuous_expectation_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain pair.1 function pair.2
  rw [same]
  exact continuous_eval.comp
    (((actualFellerSemigroup_strong_continuous_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative denseDomain function).comp continuous_fst).prodMk continuous_snd)

end
end IGSIII34.Spectral


