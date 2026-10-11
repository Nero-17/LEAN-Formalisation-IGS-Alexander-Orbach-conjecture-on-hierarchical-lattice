import IGSIII34.Spectral.ActualTransitionKernelCompletion20261011
import IGSIII34.Spectral.ScalarSpeedMeasureCompletion20261011

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

local instance actualScalarSpeedNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualScalarSpeedUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualScalarSpeedTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualScalarSpeedInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualScalarSpeedCompleteCompletion20261011 :
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

def actualScalarSpeedTimeCompletion20261011 (constant : ℝ) (positive : 0 < constant) (time : ℝ≥0) : ℝ≥0 :=
  ⟨(time : ℝ) / constant, div_nonneg time.property positive.le⟩

theorem actualScalarSpeedTime_positive_completion20261011
    (constant : ℝ) (positive : 0 < constant) (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) :
    0 < (actualScalarSpeedTimeCompletion20261011 constant positive time : ℝ) :=
  div_pos timePositive positive

/-- Heat density relative to Cμ for the time-changed actual process B(t/C). -/
def actualScalarSpeedHeatKernelCompletion20261011 (constant : ℝ) (constantPositive : 0 < constant)
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) :=
  constant⁻¹ • actualSpectralKernelContinuousCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
    (actualScalarSpeedTimeCompletion20261011 constant constantPositive time)
    (actualScalarSpeedTime_positive_completion20261011 constant constantPositive time timePositive)

/-- The transition measure uses the scaled speed measure and inverse-scaled
heat density. Both scalars cancel in the actual probability law. -/
def actualScalarSpeedTransitionKernelCompletion20261011 (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0) :
    Kernel (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
      (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :=
  if timePositive : 0 < (time : ℝ) then
    scalarSpeedTransitionKernelCompletion20261011 measure constant
      (actualSpectralKernelContinuousCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
        (actualScalarSpeedTimeCompletion20261011 constant constantPositive time)
        (actualScalarSpeedTime_positive_completion20261011 constant constantPositive time timePositive))
  else Kernel.id

theorem actualScalarSpeedTransitionKernel_identity_completion20261011
    (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0) :
    actualScalarSpeedTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data constant constantPositive time =
      actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
        (actualScalarSpeedTimeCompletion20261011 constant constantPositive time) := by
  by_cases timePositive : 0 < (time : ℝ)
  · have slowPositive := actualScalarSpeedTime_positive_completion20261011 constant constantPositive time timePositive
    simp only [actualScalarSpeedTransitionKernelCompletion20261011, dif_pos timePositive,
      actualTransitionKernelCompletion20261011, dif_pos slowPositive]
    exact scalarSpeedTransitionKernel_identity_completion20261011 measure constant constantPositive _
  · have timeZero : time = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt timePositive) time.property)
    subst time
    have slowZero : actualScalarSpeedTimeCompletion20261011 constant constantPositive 0 = 0 := by
      apply Subtype.ext
      change (0:ℝ) / constant = 0
      exact zero_div constant
    rw [slowZero, actualTransitionKernel_zero_completion20261011]
    simp [actualScalarSpeedTransitionKernelCompletion20261011]

theorem actualScalarSpeedTransitionKernel_isMarkov_completion20261011
    (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0) :
    IsMarkovKernel (actualScalarSpeedTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
      constant constantPositive time) := by
  rw [actualScalarSpeedTransitionKernel_identity_completion20261011]
  exact actualTransitionKernel_isMarkov_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data _

theorem actualScalarSpeedHeatKernel_nonnegative_completion20261011
    (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0) (timePositive : 0 < (time : ℝ))
    (first second : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    0 ≤ actualScalarSpeedHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
      constant constantPositive time timePositive (first,second) := by
  change 0 ≤ constant⁻¹ * actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
    (actualScalarSpeedTimeCompletion20261011 constant constantPositive time) first second
  exact mul_nonneg (inv_nonneg.mpr constantPositive.le)
    (actualSpectralKernel_nonnegative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data _
      (actualScalarSpeedTime_positive_completion20261011 constant constantPositive time timePositive) first second)

theorem actualScalarSpeedHeatKernel_row_integral_one_completion20261011
    (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0) (timePositive : 0 < (time : ℝ))
    (first : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    (∫ second, actualScalarSpeedHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
      constant constantPositive time timePositive (first,second) ∂scalarSpeedMeasureCompletion20261011 measure constant) = 1 := by
  change (∫ second, constant⁻¹ * actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
    (actualScalarSpeedTimeCompletion20261011 constant constantPositive time) first second ∂scalarSpeedMeasureCompletion20261011 measure constant) = 1
  have scaled := scalarSpeedMeasure_kernel_integral_completion20261011 measure constant constantPositive
    (fun second => actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
      (actualScalarSpeedTimeCompletion20261011 constant constantPositive time) first second) (fun _ => 1)
  simp only [mul_one] at scaled
  rw [scaled]
  exact actualSpectralKernel_row_integral_one_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data _
    (actualScalarSpeedTime_positive_completion20261011 constant constantPositive time timePositive) first

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualScalarSpeedTransitionKernel_feller_expectation_completion20261011
    (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0)
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    (∫ other, function other ∂actualScalarSpeedTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
      constant constantPositive time point) =
    actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative
      (actualScalarSpeedTimeCompletion20261011 constant constantPositive time) function point := by
  rw [actualScalarSpeedTransitionKernel_identity_completion20261011]
  exact actualTransitionKernel_continuous_expectation_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data
    denseDomain _ function point

end
end IGSIII34.Spectral

