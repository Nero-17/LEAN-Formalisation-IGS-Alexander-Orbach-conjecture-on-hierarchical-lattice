import IGSIII34.Spectral.ActualSpectralCoreDensityCompletion
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

local instance actualEigenIdentificationNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualEigenIdentificationUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualEigenIdentificationTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualEigenIdentificationInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualEigenIdentificationCompleteCompletion :
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
theorem actualFellerSemigroup_eigenfunction_completion
    (time : ℝ≥0) (index : data.index) :
    actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative time
      (actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index) =
    Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) •
      actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
  rw [actualFellerSemigroup_toLp_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors data.generatorNonnegative denseDomain, map_smul]
  have image : ContinuousMap.toLp 2 measure ℝ
      (actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index) = data.basis index :=
    actualContinuousEigenfunctions_toLp_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors index
  rw [image, spectralL2Semigroup_basis_completion]

include denseDomain in
theorem actualTransitionKernel_eigenfunction_expectation_completion
    (time : ℝ≥0) (index : data.index)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    (∫ other, actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index other
      ∂actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point) =
      Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) *
        actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point := by
  rw [actualTransitionKernel_continuous_expectation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain,
    actualFellerSemigroup_eigenfunction_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain]
  rfl

include denseDomain in
theorem actualTransitionKernel_unique_of_eigenfunction_moments_completion
    (time : ℝ≥0)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (candidate : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    [IsFiniteMeasure candidate]
    (moments : ∀ index : data.index,
      (∫ other, actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index other ∂candidate) =
        Real.exp (-(time : ℝ) * ((data.resolventEigenvalues index)⁻¹-1)) *
          actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point) :
    candidate = actualTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point := by
  letI := actualTransitionKernel_isMarkov_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time
  apply finite_measures_eq_of_dense_continuous_core_completion
    (actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data)
    (actual_spectral_eigenfunctions_span_dense_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain)
  intro index
  rw [moments index, actualTransitionKernel_eigenfunction_expectation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain]

end
end IGSIII34.Spectral