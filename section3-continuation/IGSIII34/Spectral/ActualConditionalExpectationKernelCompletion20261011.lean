import IGSIII34.Spectral.ActualConditionalCoreIdentificationCompletion20261011
import IGSIII34.Spectral.ConditionalExpectationMomentsCompletion20261011
import Mathlib.Probability.Kernel.CondDistrib
import IGSIII34.Spectral.ContinuousIntegralCoreUniquenessCompletion20261011
import IGSIII34.Spectral.DenseScaledHilbertImageCompletion20261011
import IGSIII34.Spectral.ContinuousKernelTransitionIntegralCompletion20261011
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Actual transition kernels: positive times use the proved natural heat
kernel density and time zero is the identity kernel. Their continuous
expectations are precisely the constructed Feller semigroup. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
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

local instance actualConditionalExpectationNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualConditionalExpectationUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualConditionalExpectationTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualConditionalExpectationInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualConditionalExpectationCompleteCompletion20261011 :
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
theorem actual_conditional_distribution_eq_transition_of_spectral_condExp_completion20261011
    {Outcome History : Type*} [MeasurableSpace Outcome] [MeasurableSpace History]
    (law : Measure Outcome) [IsFiniteMeasure law]
    (history : Outcome → History) (historyMeasurable : Measurable history)
    (future : Outcome → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (futureMeasurable : AEMeasurable future law)
    (state : History → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (stateMeasurable : Measurable state) (time : ℝ≥0) :
    letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := nonempty_of_isProbabilityMeasure measure
    (∀ index : data.index, law[fun outcome => actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index (future outcome) |
      (inferInstance : MeasurableSpace History).comap history] =ᵐ[law]
        (fun outcome => Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) *
          actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index (state (history outcome)))) →
    condDistrib future history law =ᵐ[law.map history]
      (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time).comap state stateMeasurable := by
  letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := nonempty_of_isProbabilityMeasure measure
  intro conditionalIdentity
  apply actual_transition_kernel_ae_unique_of_core_moments_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain
    (law.map history) (condDistrib future history law) state stateMeasurable time
  intro index
  apply conditional_distribution_moment_of_conditional_expectation_completion20261011 law history historyMeasurable future futureMeasurable
    (actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index)
    (actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index).continuous.stronglyMeasurable
  · apply Integrable.of_bound
      ((actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index).continuous.measurable.comp_aemeasurable futureMeasurable).aestronglyMeasurable
      ‖actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index‖
    exact Eventually.of_forall (fun outcome => ContinuousMap.norm_coe_le_norm _ (future outcome))
  · exact measurable_const.mul
      ((actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index).continuous.measurable.comp stateMeasurable)
  · exact conditionalIdentity index

end
end IGSIII34.Spectral