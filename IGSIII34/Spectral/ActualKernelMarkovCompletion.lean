import IGSIII34.Spectral.ActualSpectralDataCompletion
import IGSIII34.Spectral.KernelSeriesOperatorCompletion
import IGSIII34.Spectral.ContinuousKernelMarkovCompletion
import IGSIII34.Spectral.ActualFellerMarkovCompletion

/-! The actual continuous spectral kernel represents the proved Feller
semigroup, is nonnegative at every pair of points, and has row mass one. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology BoundedContinuousFunction NNReal
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualKernelMarkovNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualKernelMarkovUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualKernelMarkovTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualKernelMarkovInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualKernelMarkovCompleteCompletion :
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

def actualSpectralKernelContinuousCompletion (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) :
    C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) ×
      UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) :=
  ⟨fun pair => actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time pair.1 pair.2,
    (actualSpectralData_heat_continuousOn_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => timePositive)⟩

theorem actualSpectralKernel_operator_identification_completion
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ)) :
    (ContinuousMap.toLp 2 measure ℝ).comp
      (continuousKernelL2OperatorCompletion measure
        (actualSpectralKernelContinuousCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)) =
    spectralL2SemigroupCompletion data.basis (fun index => (data.resolventEigenvalues index)⁻¹-1) data.generatorNonnegative time := by
  apply spectral_kernel_operator_identification_completion measure
    (fun index => (data.resolventEigenvalues index)⁻¹-1)
    (actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data)
    data.generatorNonnegative data.generatorDiverge
    (‖actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure‖ ^ 2) (sq_nonneg _)
    _ data.basis _ time timePositive _ (fun _ _ => rfl)
  · exact continuousResolventEigenfunctions_evaluation_bound_completion
      (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualFormHilbertBasisCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors)
      data.resolventEigenvalues data.eigenvaluesPositive
  · exact actualContinuousEigenfunctions_toLp_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors

theorem actualSpectralKernel_nonnegative_completion
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ))
    (first second : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    0 ≤ actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time first second := by
  apply continuous_kernel_pointwise_nonnegative_completion measure
    (actualSpectralKernelContinuousCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive) _ first second
  intro forcing nonnegative
  have identification := congrArg (fun operator => operator forcing)
    (actualSpectralKernel_operator_identification_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
  simp only [ContinuousLinearMap.comp_apply] at identification
  rw [identification]
  exact actual_spectral_semigroup_positive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative time forcing nonnegative

theorem actualSpectralKernel_row_integral_one_completion
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ))
    (first : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    (∫ second, actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time first second ∂measure) = 1 := by
  apply continuous_kernel_row_integral_one_completion measure
    (actualSpectralKernelContinuousCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive) _ first
  have identification := congrArg (fun operator => operator (ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const _ (1 : ℝ))))
    (actualSpectralKernel_operator_identification_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
  simp only [ContinuousLinearMap.comp_apply] at identification
  rw [identification]
  exact actual_spectral_semigroup_canonical_constant_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative time 1

theorem actualSpectralKernel_feller_representation_completion
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)
    (time : ℝ≥0) (timePositive : 0 < (time : ℝ))
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    continuousKernelL2OperatorCompletion measure
      (actualSpectralKernelContinuousCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
      (ContinuousMap.toLp 2 measure ℝ function) =
    actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative time function := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
  have identification := congrArg (fun operator => operator (ContinuousMap.toLp 2 measure ℝ function))
    (actualSpectralKernel_operator_identification_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time timePositive)
  exact identification.trans (actualFellerSemigroup_toLp_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative denseDomain time function).symm

end
end IGSIII34.Spectral


