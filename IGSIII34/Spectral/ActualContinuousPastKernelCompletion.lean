import IGSIII34.Spectral.ActualConditionalCoreIdentificationCompletion
import IGSIII34.Spectral.ContinuousPastConditionalMomentCompletion
import Mathlib.Probability.Kernel.CondDistrib
import IGSIII34.Spectral.ContinuousIntegralCoreUniquenessCompletion
import IGSIII34.Spectral.DenseScaledHilbertImageCompletion
import IGSIII34.Spectral.ContinuousKernelTransitionIntegralCompletion
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

local instance actualContinuousPastNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualContinuousPastUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualContinuousPastTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualContinuousPastInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualContinuousPastCompleteCompletion :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

variable [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actual_transition_conditional_of_continuous_past_spectral_tests_completion
    {Outcome History : Type*} [MeasurableSpace Outcome]
    [MetricSpace History] [CompactSpace History] [MeasurableSpace History] [BorelSpace History]
    (law : Measure Outcome) [IsFiniteMeasure law]
    (history : Outcome → History) (historyMeasurable : Measurable history)
    (future : Outcome → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (futureMeasurable : AEMeasurable future law)
    [(law.map history).WeaklyRegular]
    (state : History → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (stateMeasurable : Measurable state) (time : ℝ≥0) :
    letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := nonempty_of_isProbabilityMeasure measure
    (∀ index : data.index, ∀ test : C(History, ℝ),
      (∫ outcome, test (history outcome) * actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index (future outcome) ∂law) =
        Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) *
          ∫ outcome, test (history outcome) * actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index (state (history outcome)) ∂law) →
    condDistrib future history law =ᵐ[law.map history]
      (actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time).comap state stateMeasurable := by
  letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := nonempty_of_isProbabilityMeasure measure
  intro paired
  apply actual_transition_kernel_ae_unique_of_core_moments_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain
    (law.map history) (condDistrib future history law) state stateMeasurable time
  intro index
  apply conditional_moment_of_continuous_past_tests_completion law history historyMeasurable future futureMeasurable
    (actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index)
    (fun retained => Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) *
      actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index (state retained))
    (measurable_const.mul ((actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index).continuous.measurable.comp stateMeasurable))
    (‖Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1))‖ *
      ‖actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index‖)
  · apply Eventually.of_forall
    intro retained
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ (state retained)) (norm_nonneg _)
  · intro test
    calc
      _ = Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) *
          ∫ outcome, test (history outcome) * actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index (state (history outcome)) ∂law := paired index test
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun _ => by ring)

end
end IGSIII34.Spectral
