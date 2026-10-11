import IGSIII34.Spectral.FormSemigroupIntertwiningCompletion20261011
import IGSIII34.Spectral.ActualSemigroupMarkovCompletion20261011

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

local instance actualFellerEnergyNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerEnergyUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualFellerEnergyTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualFellerEnergyInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerEnergyCompleteCompletion20261011 :
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
  {Index : Type*} (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
  (eigenvaluesPositive : ∀ index, 0 < eigenvalues index)
  (eigenvectors : ∀ index, actualL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (basis index) = eigenvalues index • basis index)
  (generatorNonnegative : ∀ index, 0 ≤ (eigenvalues index)⁻¹-1)

theorem actualFormContinuousEmbedding_toLp_basis_completion20261011 (index : Index) :
    ContinuousMap.toLp 2 measure ℝ
      (actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualFormHilbertBasisCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          basis eigenvalues eigenvaluesPositive eigenvectors index)) = Real.sqrt (eigenvalues index) • basis index := by
  have image := actualContinuousEigenfunctions_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors index
  rw [actualContinuousEigenfunctionsCompletion20261011, continuousResolventEigenfunctionsCompletion20261011, map_smul] at image
  have scaled := congrArg (fun vector => Real.sqrt (eigenvalues index) • vector) image
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (eigenvaluesPositive index)).ne', one_smul] at scaled
  exact scaled

def actualFormContinuousSemigroupCompletion20261011 (time : ℝ≥0) :=
  (actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).comp
    (spectralL2SemigroupCompletion20261011
      (actualFormHilbertBasisCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors)
      (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time)

theorem actualFormContinuousSemigroup_continuous_completion20261011
    (potential : coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor))
      (anchoredResolventBilinear_symmetric_completion20261011 _ _)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)) :
    Continuous (fun time : ℝ≥0 => actualFormContinuousSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential) :=
  form_semigroup_continuous_representative_completion20261011
    (actualFormHilbertBasisCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors)
    (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative
    (actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) potential

theorem actualFormContinuousSemigroup_toLp_completion20261011
    (time : ℝ≥0) :
    (ContinuousMap.toLp 2 measure ℝ).comp
      (actualFormContinuousSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time) =
    (spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time).comp
      ((ContinuousMap.toLp 2 measure ℝ).comp
        (actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)) := by
  rw [actualFormContinuousSemigroupCompletion20261011, ← ContinuousLinearMap.comp_assoc]
  exact form_semigroup_intertwining_completion20261011
    (actualFormHilbertBasisCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors) basis _
    (fun index => Real.sqrt (eigenvalues index))
    (actualFormContinuousEmbedding_toLp_basis_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors)
    (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time

end
end IGSIII34.Spectral



