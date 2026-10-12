import IGSIII34.Spectral.FormSemigroupIntertwiningCompletion
import IGSIII34.Spectral.ActualSemigroupMarkovCompletion

/-! On the actual dense finite-energy domain the spectral semigroup has a
continuous-function representative with continuous dependence on all times,
including time zero. Its L² representative is the true constructed P_t. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
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

local instance actualFellerEnergyNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerEnergyUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualFellerEnergyTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualFellerEnergyInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerEnergyCompleteCompletion :
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
  {Index : Type*} (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
  (eigenvaluesPositive : ∀ index, 0 < eigenvalues index)
  (eigenvectors : ∀ index, actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (basis index) = eigenvalues index • basis index)
  (generatorNonnegative : ∀ index, 0 ≤ (eigenvalues index)⁻¹-1)

theorem actualFormContinuousEmbedding_toLp_basis_completion (index : Index) :
    ContinuousMap.toLp 2 measure ℝ
      (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualFormHilbertBasisCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          basis eigenvalues eigenvaluesPositive eigenvectors index)) = Real.sqrt (eigenvalues index) • basis index := by
  have image := actualContinuousEigenfunctions_toLp_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors index
  rw [actualContinuousEigenfunctionsCompletion, continuousResolventEigenfunctionsCompletion, map_smul] at image
  have scaled := congrArg (fun vector => Real.sqrt (eigenvalues index) • vector) image
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (eigenvaluesPositive index)).ne', one_smul] at scaled
  exact scaled

def actualFormContinuousSemigroupCompletion (time : ℝ≥0) :=
  (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).comp
    (spectralL2SemigroupCompletion
      (actualFormHilbertBasisCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors)
      (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time)

theorem actualFormContinuousSemigroup_continuous_completion
    (potential : coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion
        (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor))
      (anchoredResolventBilinear_symmetric_completion _ _)
      (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)) :
    Continuous (fun time : ℝ≥0 => actualFormContinuousSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential) :=
  form_semigroup_continuous_representative_completion
    (actualFormHilbertBasisCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors)
    (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative
    (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) potential

theorem actualFormContinuousSemigroup_toLp_completion
    (time : ℝ≥0) :
    (ContinuousMap.toLp 2 measure ℝ).comp
      (actualFormContinuousSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time) =
    (spectralL2SemigroupCompletion basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time).comp
      ((ContinuousMap.toLp 2 measure ℝ).comp
        (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)) := by
  rw [actualFormContinuousSemigroupCompletion, ← ContinuousLinearMap.comp_assoc]
  exact form_semigroup_intertwining_completion
    (actualFormHilbertBasisCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors) basis _
    (fun index => Real.sqrt (eigenvalues index))
    (actualFormContinuousEmbedding_toLp_basis_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors)
    (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time

end
end IGSIII34.Spectral



