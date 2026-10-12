import IGSIII34.Spectral.ActualKernelMarkovCompletion
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

local instance actualTransitionMarkovNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualTransitionMarkovUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualTransitionMarkovTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualTransitionMarkovInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualTransitionMarkovCompleteCompletion :
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

def actualTransitionKernelCompletion (time : ℝ≥0) :
    Kernel (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
      (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :=
  if timePositive : 0 < (time : ℝ) then
    continuousTransitionKernelCompletion measure
      (actualSpectralKernelContinuousCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
  else Kernel.id

theorem actualTransitionKernel_isMarkov_completion (time : ℝ≥0) :
    IsMarkovKernel (actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time) := by
  unfold actualTransitionKernelCompletion
  split_ifs with timePositive
  · exact continuousTransitionKernel_isMarkov_completion measure _
      (actualSpectralKernel_nonnegative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
      (actualSpectralKernel_row_integral_one_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
  · infer_instance

def actualTransitionProbabilityCompletion (time : ℝ≥0)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    ProbabilityMeasure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :=
  letI := actualTransitionKernel_isMarkov_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time
  ⟨actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point, inferInstance⟩

theorem actualTransitionKernel_zero_completion :
    actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data 0 = Kernel.id := by
  simp [actualTransitionKernelCompletion]

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualTransitionKernel_continuous_expectation_completion
    (time : ℝ≥0)
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    (∫ other, function other ∂actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point) =
    actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative time function point := by
  by_cases timePositive : 0 < (time : ℝ)
  · rw [actualTransitionKernelCompletion, dif_pos timePositive,
      continuousTransitionKernel_continuous_expectation_completion measure _
        (actualSpectralKernel_nonnegative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)]
    exact congrArg (fun output => output point)
      (actualSpectralKernel_feller_representation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain time timePositive function)
  · have timeZero : time = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt timePositive) time.property)
    rw [timeZero, actualTransitionKernel_zero_completion, Kernel.id_apply,
      actualFellerSemigroup_zero_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative denseDomain]
    simp

include denseDomain in
theorem actualTransitionKernel_add_completion (first second : ℝ≥0) :
    (actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data second) ∘ₖ
      (actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data first) =
    actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data (first+second) := by
  letI := actualTransitionKernel_isMarkov_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data first
  letI := actualTransitionKernel_isMarkov_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data second
  letI := actualTransitionKernel_isMarkov_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data (first+second)
  ext point : 1
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro function
  rw [Kernel.integral_comp (function.integrable _)]
  have innerExpectation : (fun other => ∫ last, function last ∂actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data second other) =
      fun other => actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative second function.toContinuousMap other := by
    funext other
    exact actualTransitionKernel_continuous_expectation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain second function.toContinuousMap other
  rw [innerExpectation,
    actualTransitionKernel_continuous_expectation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain]
  have outerExpectation := actualTransitionKernel_continuous_expectation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain (first+second) function.toContinuousMap point
  change _ = (∫ x, function.toContinuousMap x ∂actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data (first+second) point)
  rw [outerExpectation]
  exact congrArg (fun output => output point)
    (actualFellerSemigroup_add_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative denseDomain first second function.toContinuousMap)

end
end IGSIII34.Spectral


