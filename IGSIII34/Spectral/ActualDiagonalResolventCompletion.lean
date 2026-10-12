import IGSIII34.Spectral.ActualContinuousKernelCompletion
import IGSIII34.Spectral.ParameterFormHilbertCompletion
import IGSIII34.Spectral.HeatLaplaceIdentityCompletion
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

local instance actualDiagonalNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualDiagonalUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualDiagonalTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualDiagonalInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualDiagonalCompleteCompletion :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]


open IGSIII34.Diffusion

theorem actualParameterResolventBilinear_self_completion
    (parameter : ℝ)
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    parameterAnchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      parameter potential potential =
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
      parameter * ∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 ∂measure := by
  rw [parameterAnchoredResolventBilinear_apply_completion, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, actualAnchorEvaluation_apply_completion,
    actualEnergyL2Embedding_norm_square_completion,
    actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential]
  ring

variable [measure.IsOpenPosMeasure]

theorem actualContinuousFormEvaluation_apply_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    continuousFormEvaluationCompletion
      (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) point potential =
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point := rfl

theorem actualContinuousEigenfunctions_evaluation_completion {Index : Type*}
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
    (positiveEigenvalues : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (basis index) = eigenvalues index • basis index)
    (index : Index) (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    actualContinuousEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues positiveEigenvalues eigenvectors index point =
      (eigenvalues index)⁻¹ *
        continuousFormEvaluationCompletion
          (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) point
          ((actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).continuousLinearEquivOfBilin.symm
            ((actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).adjoint (basis index))) := by
  rw [actualContinuousEigenfunctionsCompletion, continuousResolventEigenfunctionsCompletion,
    actualFormHilbertBasisCompletion, anchoredFormHilbertBasisCompletion,
    resolventEnergyHilbertBasis_apply_completion]
  rw [normalisedResolventEigenvectorsCompletion, map_smul]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  change (Real.sqrt (eigenvalues index))⁻¹ *
    ((Real.sqrt (eigenvalues index))⁻¹ *
      continuousFormEvaluationCompletion
        (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) point
        ((actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).continuousLinearEquivOfBilin.symm
          ((actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).adjoint (basis index)))) = _
  rw [← mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (positiveEigenvalues index).le]

theorem actual_diagonal_resolvent_spectral_identity_completion {Index : Type*}
    (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
    (positiveEigenvalues : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (basis index) = eigenvalues index • basis index)
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    HasSum (fun index =>
      actualContinuousEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues positiveEigenvalues eigenvectors index point ^ 2 /
          (parameter + ((eigenvalues index)⁻¹ - 1)))
      (sSup (Set.range (fun potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor =>
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 /
          (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
            (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
            parameter * ∫ other, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ^ 2 ∂measure)))) := by
  have identity := parameterFormEvaluation_spectral_identity_completion
    (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter parameterAtLeastOne
    (actualEnergyL2Embedding_injective_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    basis eigenvalues positiveEigenvalues eigenvectors
    (continuousFormEvaluationCompletion
      (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) point)
  simp only [actualContinuousEigenfunctions_evaluation_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues positiveEigenvalues eigenvectors, add_sub_assoc]
  simpa only [actualParameterResolventBilinear_self_completion,
    actualContinuousFormEvaluation_apply_completion, add_sub_assoc] using identity

end
end IGSIII34.Spectral
