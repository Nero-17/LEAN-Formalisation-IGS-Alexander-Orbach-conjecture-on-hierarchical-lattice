import IGSIII34.Spectral.ActualEigenbasisCompletion20261011
import IGSIII34.Spectral.AnchoredFormSpectrumCompletion20261011
import IGSIII34.Spectral.FormEigenvectorsImageCompletion20261011
import IGSIII34.Spectral.ContinuousSpectralKernelCompletion20261011
import IGSIII34.Spectral.CompactEigenbasisCompletion20261011
import IGSIII34.Spectral.ResolventEigenvaluesCompletion20261011
import IGSIII34.Spectral.ActualResolventCompletion20261011
import IGSIII34.Spectral.ActualCompactEmbeddingCompletion20261011
import IGSIII34.Spectral.AnchoredResolventCompletion20261011
import IGSIII34.Forms.L2ClosednessCompletion20261011
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

local instance actualHeatNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualHeatUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualHeatTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualHeatInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualHeatCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]


def actualFormContinuousEmbeddingCompletion20261011 :=
  (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).comp
    (coerciveFormEquivCompletion20261011
      (anchoredResolventBilinearCompletion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor))
      (anchoredResolventBilinear_symmetric_completion20261011 _ _)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)).toContinuousLinearMap

variable [measure.IsOpenPosMeasure]

def actualFormHilbertBasisCompletion20261011 {Index : Type*}
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
    (positiveEigenvalues : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, actualL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (basis index) = eigenvalues index • basis index) :=
  anchoredFormHilbertBasisCompletion20261011
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualEnergyL2Embedding_injective_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    basis eigenvalues positiveEigenvalues eigenvectors

def actualContinuousEigenfunctionsCompletion20261011 {Index : Type*}
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
    (positiveEigenvalues : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, actualL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (basis index) = eigenvalues index • basis index) :=
  continuousResolventEigenfunctionsCompletion20261011
    (actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualFormHilbertBasisCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues positiveEigenvalues eigenvectors) eigenvalues

theorem actualContinuousEigenfunctions_toLp_completion20261011 {Index : Type*}
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
    (positiveEigenvalues : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, actualL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (basis index) = eigenvalues index • basis index) (index : Index) :
    ContinuousMap.toLp 2 measure ℝ
      (actualContinuousEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues positiveEigenvalues eigenvectors index) = basis index := by
  rw [actualContinuousEigenfunctionsCompletion20261011, continuousResolventEigenfunctionsCompletion20261011, map_smul]
  have image : ContinuousMap.toLp 2 measure ℝ
      (actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualFormHilbertBasisCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          basis eigenvalues positiveEigenvalues eigenvectors index)) = Real.sqrt (eigenvalues index) • basis index := by
    let embedding := actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    let evaluation := actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    let coercive := actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    exact resolventEnergyHilbertBasis_embedding_completion20261011
      (anchoredFormEmbeddingCompletion20261011 embedding evaluation coercive)
      (anchoredFormEmbedding_injective_completion20261011 embedding evaluation coercive
        (actualEnergyL2Embedding_injective_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure))
      (anchoredFormSolutionCompletion20261011 embedding evaluation coercive)
      (anchoredFormSolution_variational_completion20261011 embedding evaluation coercive)
      basis eigenvalues positiveEigenvalues (fun index => by
        rw [anchoredFormEmbedding_solution_completion20261011]
        exact eigenvectors index) index
  rw [image, smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (positiveEigenvalues index)).ne', one_smul]

theorem exists_actual_continuous_spectral_kernel_completion20261011 [measure.WeaklyRegular]
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier) :
    ∃ Index : Type, ∃ eigenfunctions : Index → C(UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ),
      ∃ eigenvalues : Index → ℝ,
      Countable Index ∧ (∀ index, 0 ≤ eigenvalues index) ∧ Tendsto eigenvalues cofinite atTop ∧
      (∃ basis : HilbertBasis Index ℝ (Lp ℝ 2 measure),
        ∀ index, ContinuousMap.toLp 2 measure ℝ (eigenfunctions index) = basis index) ∧
      (∀ index, actualL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (ContinuousMap.toLp 2 measure ℝ (eigenfunctions index)) =
          (1 + eigenvalues index)⁻¹ • ContinuousMap.toLp 2 measure ℝ (eigenfunctions index)) ∧
      ContinuousOn (fun point : ℝ × UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) ×
        UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) =>
        indexedSpectralHeatKernelCompletion20261011 eigenvalues (fun index => eigenfunctions index)
          point.1 point.2.1 point.2.2) {point | 0 < point.1} := by
  obtain ⟨Index, basis, eigenvalues, countable, positiveEigenvalues, eigenvectors, nonnegative, diverge⟩ :=
    exists_actual_resolvent_eigenbasis_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain
  refine ⟨Index,
    actualContinuousEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues (fun index => (positiveEigenvalues index).1) eigenvectors,
    (fun index => (eigenvalues index)⁻¹ - 1), countable, nonnegative, diverge,
    ⟨basis, actualContinuousEigenfunctions_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues (fun index => (positiveEigenvalues index).1) eigenvectors⟩, ?_, ?_⟩
  · intro index
    rw [actualContinuousEigenfunctions_toLp_completion20261011]
    have denominator : 1 + ((eigenvalues index)⁻¹ - 1) = (eigenvalues index)⁻¹ := by ring
    rw [denominator, inv_inv]
    exact eigenvectors index
  · exact continuousResolventEigenfunctions_heat_kernel_continuousOn_completion20261011 _ _ _
      (fun index => (positiveEigenvalues index).1) nonnegative diverge

end
end IGSIII34.Spectral
