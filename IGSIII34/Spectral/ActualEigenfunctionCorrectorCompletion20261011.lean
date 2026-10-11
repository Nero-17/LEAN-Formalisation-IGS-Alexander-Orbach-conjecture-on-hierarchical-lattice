import IGSIII34.Diffusion.ActualContinuousObjectiveCompletion20261011
import IGSIII34.Spectral.ActualSpectralCoreDensityCompletion20261011
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

local instance actualEigenCorrectorNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualEigenCorrectorUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualEigenCorrectorTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualEigenCorrectorInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualEigenCorrectorCompleteCompletion20261011 :
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

theorem actual_eigenfunction_resolvent_corrector_completion20261011
    (index : data.index) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        1 le_rfl ((1 + ((data.resolventEigenvalues index)⁻¹ - 1)) •
          actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index)) =
    actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
  have image : ContinuousMap.toLp 2 measure ℝ
      (actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index) = data.basis index :=
    actualContinuousEigenfunctions_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors index
  change actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (parameterEnergySolutionCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      1 le_rfl (ContinuousMap.toLp 2 measure ℝ ((1 + ((data.resolventEigenvalues index)⁻¹ - 1)) •
        actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index))) = _
  rw [map_smul, image, map_smul, map_smul,
    parameterL2Solution_eigenvalue_completion20261011 _ _ _ 1 le_rfl _ _ (data.eigenvaluesPositive index) (data.eigenvectors index)]
  have coefficient : (1 + ((data.resolventEigenvalues index)⁻¹ - 1)) *
      (data.resolventEigenvalues index / (1 + (1 - 1) * data.resolventEigenvalues index)) = 1 := by
    field_simp [(data.eigenvaluesPositive index).ne']
    <;> ring
  rw [smul_smul, coefficient, one_smul]

end
end IGSIII34.Spectral
