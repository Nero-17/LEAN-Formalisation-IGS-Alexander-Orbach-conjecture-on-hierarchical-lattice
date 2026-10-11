import IGSIII34.Spectral.ActualEnergyFellerCompletion20261011
import IGSIII34.Spectral.ContinuousLpOrderCompletion20261011

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

local instance actualFellerSupNormNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerSupNormUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualFellerSupNormTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualFellerSupNormInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerSupNormCompleteCompletion20261011 :
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

theorem actualEnergyConstant_toLp_completion20261011 (constant : ℝ) :
    actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) =
    ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const _ constant) := by
  apply Lp.ext
  filter_upwards [actualEnergyL2Embedding_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) measure (ContinuousMap.const _ constant)] with point actualAt constantAt
  rw [actualAt, constantAt, actualEnergyConstant_extension_completion20261011]
  rfl

include eigenvaluesPositive eigenvectors in
theorem actual_spectral_semigroup_canonical_constant_completion20261011 (time : ℝ≥0) (constant : ℝ) :
    spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time
      (ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const _ constant)) =
    ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const _ constant) := by
  rw [← actualEnergyConstant_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure constant]
  exact actual_spectral_semigroup_constant_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time constant

theorem actualFormContinuousSemigroup_supnorm_completion20261011
    (time : ℝ≥0)
    (potential : coerciveFormHilbertCompletion20261011
      (anchoredResolventBilinearCompletion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor))
      (anchoredResolventBilinear_symmetric_completion20261011 _ _)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)) :
    ‖actualFormContinuousSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential‖ ≤
    ‖actualFormContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential‖ := by
  apply continuousMap_operator_norm_bound_completion20261011 measure
    (spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time)
    (actual_spectral_semigroup_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time)
    (actual_spectral_semigroup_canonical_constant_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time)
  exact congrArg (fun operator => operator potential)
    (actualFormContinuousSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time)

end
end IGSIII34.Spectral


