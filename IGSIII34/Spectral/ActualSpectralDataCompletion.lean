import IGSIII34.Spectral.ActualDiagonalResolventCompletion
import IGSIII34.Spectral.ActualVariationalBoundsCompletion
import IGSIII34.Spectral.HeatDiagonalAnalysisCompletion
import IGSIII34.Spectral.SemigroupContinuityCompletion
import IGSIII34.Spectral.ActualEigenbasisCompletion
import IGSIII34.Spectral.AnchoredFormSpectrumCompletion
import IGSIII34.Spectral.FormEigenvectorsImageCompletion
import IGSIII34.Spectral.ContinuousSpectralKernelCompletion
import IGSIII34.Spectral.CompactEigenbasisCompletion
import IGSIII34.Spectral.ResolventEigenvaluesCompletion
import IGSIII34.Spectral.ActualResolventCompletion
import IGSIII34.Spectral.ActualCompactEmbeddingCompletion
import IGSIII34.Spectral.AnchoredResolventCompletion
import IGSIII34.Forms.L2ClosednessCompletion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! The actual compact L² resolvent is constructed by Lax-Milgram from the
proved electrical energy. The mass-measure input is kept explicit until the
actual electrical boundary pushforward is assembled. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace
open scoped Topology BoundedContinuousFunction

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualDataNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualDataUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualDataTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualDataInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualDataCompleteCompletion :
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

/-- Spectral data of the actual constructed L2 resolvent. The existence
theorem below derives every field from the actual energy domain. -/
structure ActualSpectralDataCompletion where
  index : Type
  countable : Countable index
  basis : HilbertBasis index ℝ (Lp ℝ 2 measure)
  resolventEigenvalues : index → ℝ
  eigenvaluesPositive : ∀ index, 0 < resolventEigenvalues index
  atMostOne : ∀ index, resolventEigenvalues index ≤ 1
  eigenvectors : ∀ index,
    actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (basis index) = resolventEigenvalues index • basis index
  generatorNonnegative : ∀ index, 0 ≤ (resolventEigenvalues index)⁻¹ - 1
  generatorDiverge : Tendsto (fun index => (resolventEigenvalues index)⁻¹ - 1) cofinite atTop

theorem exists_actual_spectral_data_completion [measure.WeaklyRegular]
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier) :
    Nonempty (ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) := by
  obtain ⟨Index, basis, eigenvalues, countable, positiveEigenvalues, eigenvectors, nonnegative, diverge⟩ :=
    exists_actual_resolvent_eigenbasis_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain
  exact ⟨⟨Index, countable, basis, eigenvalues, (fun index => (positiveEigenvalues index).1),
    (fun index => (positiveEigenvalues index).2), eigenvectors, nonnegative, diverge⟩⟩

variable (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

def actualSpectralEigenfunctionsCompletion :=
  actualContinuousEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors

def actualSpectralHeatKernelCompletion :=
  indexedSpectralHeatKernelCompletion (fun index => (data.resolventEigenvalues index)⁻¹ - 1)
    (fun index => actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index)

theorem actualSpectralData_weighted_sum_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    HasSum (fun index => actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point ^ 2 /
      (parameter + ((data.resolventEigenvalues index)⁻¹ - 1)))
      (actualDiagonalVariationalResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point) :=
  actual_diagonal_resolvent_spectral_identity_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors parameter parameterAtLeastOne point

theorem actualSpectralData_laplace_variational_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    diagonalLaplace (fun time => actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point point) parameter =
      actualDiagonalVariationalResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point := by
  letI := data.countable
  have identity := indexed_spectral_heat_diagonal_laplace_completion
    (fun index => (data.resolventEigenvalues index)⁻¹ - 1)
    (fun index => actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index)
    data.generatorNonnegative parameter (zero_lt_one.trans_le parameterAtLeastOne) point
    (actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point parameter parameterAtLeastOne).summable
  exact identity.trans (actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point parameter parameterAtLeastOne).tsum_eq

theorem actualSpectralData_heat_continuousOn_completion :
    ContinuousOn (fun point : ℝ × UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) ×
      UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) =>
      actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point.1 point.2.1 point.2.2)
      {point | 0 < point.1} :=
  continuousResolventEigenfunctions_heat_kernel_continuousOn_completion _ _ _ data.eigenvaluesPositive data.generatorNonnegative data.generatorDiverge

theorem actualSpectralData_diagonal_nonnegative_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) (time : ℝ) :
    0 ≤ actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point point := by
  apply tsum_nonneg
  intro index
  have := mul_nonneg (Real.exp_pos (-time * ((data.resolventEigenvalues index)⁻¹ - 1))).le
    (sq_nonneg (actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point))
  simpa only [pow_two, mul_assoc] using this

theorem actualSpectralData_diagonal_antitone_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    AntitoneOn (fun time => actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point point) (Set.Ioi 0) := by
  have identity := diagonal_heat_series_antitone_completion
    (fun index => (data.resolventEigenvalues index)⁻¹ - 1)
    (fun index => actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point ^ 2)
    data.generatorNonnegative (fun index => sq_nonneg _) data.generatorDiverge
    (actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point 1 le_rfl).summable
  simpa only [actualSpectralHeatKernelCompletion, indexedSpectralHeatKernelCompletion, pow_two, mul_assoc] using identity

theorem actualSpectralData_diagonal_integrable_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    IntegrableOn (fun time => Real.exp (-parameter * time) *
      actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point point) (Set.Ioi 0) := by
  letI := data.countable
  have base := (actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point 1 le_rfl).summable
  have identity := diagonal_spectral_series_integrable_completion
    (fun index => (data.resolventEigenvalues index)⁻¹ - 1)
    (fun index => actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point ^ 2)
    data.generatorNonnegative (fun index => sq_nonneg _) parameter parameterPositive
    (diagonal_resolvent_summable_all_positive_completion _ _ data.generatorNonnegative (fun index => sq_nonneg _) base parameter parameterPositive)
  simpa only [actualSpectralHeatKernelCompletion, indexedSpectralHeatKernelCompletion, pow_two, mul_assoc] using identity

end
end IGSIII34.Spectral
