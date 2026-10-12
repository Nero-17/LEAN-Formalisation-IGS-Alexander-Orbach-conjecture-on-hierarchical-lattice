import IGSIII34.Spectral.ActualFormSemigroupSupNormCompletion
import IGSIII34.Spectral.DenseOrbitContinuityCompletion

/-! The genuine Feller semigroup is obtained by continuous extension of the
proved sup-norm contraction on the actual uniformly dense energy domain.
Its L² action agrees with the actual spectral diffusion semigroup. -/
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

local instance actualFullFellerNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFullFellerUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualFullFellerTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualFullFellerInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFullFellerCompleteCompletion :
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

def actualFellerSemigroupCompletion (time : ℝ≥0) :=
  (actualFormContinuousSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time).toLinearMap.extendOfNorm
      (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).toLinearMap

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualFormContinuousEmbedding_dense_completion :
    DenseRange (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) := by
  have domainRange := completionEnergyDomain_eq_extension_range
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
  have denseEmbedding : DenseRange (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) := by
    change Dense (Set.range (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks))
    exact (congrArg Dense domainRange).mp denseDomain
  exact denseEmbedding.comp
    (coerciveFormEquivCompletion
      (anchoredResolventBilinearCompletion
        (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor))
      (anchoredResolventBilinear_symmetric_completion _ _)
      (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)).surjective.denseRange
    (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).continuous

include denseDomain in
theorem actualFellerSemigroup_energy_calibration_completion
    (time : ℝ≥0)
    (potential : coerciveFormHilbertCompletion
      (anchoredResolventBilinearCompletion
        (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor))
      (anchoredResolventBilinear_symmetric_completion _ _)
      (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)) :
    actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time
      (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential) =
    actualFormContinuousSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential :=
  LinearMap.extendOfNorm_eq
    (actualFormContinuousEmbedding_dense_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain)
    ⟨1, fun potential => by simpa only [one_mul, ContinuousLinearMap.coe_coe] using (actualFormContinuousSemigroup_supnorm_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential)⟩ potential

include denseDomain in
theorem actualFellerSemigroup_supnorm_completion
    (time : ℝ≥0)
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    ‖actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time function‖ ≤ ‖function‖ := by
  exact (LinearMap.norm_extendOfNorm_apply_le
    (actualFormContinuousEmbedding_dense_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain) 1
    (fun potential => by simpa only [one_mul, ContinuousLinearMap.coe_coe] using (actualFormContinuousSemigroup_supnorm_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential)) function).trans_eq (one_mul _)

include denseDomain in
theorem actualFellerSemigroup_strong_continuous_completion
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    Continuous (fun time : ℝ≥0 => actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time function) := by
  apply continuous_orbit_of_dense_continuous_orbits_completion
    (actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative)
    (actualFellerSemigroup_supnorm_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain)
    (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualFormContinuousEmbedding_dense_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain)
  intro potential
  have same : (fun time : ℝ≥0 => actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time
      (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential)) =
      (fun time : ℝ≥0 => actualFormContinuousSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time potential) := by
    funext time
    exact actualFellerSemigroup_energy_calibration_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain time potential
  rw [same]
  exact actualFormContinuousSemigroup_continuous_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative potential

include denseDomain in
theorem actualFellerSemigroup_toLp_completion
    (time : ℝ≥0)
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    ContinuousMap.toLp 2 measure ℝ
      (actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time function) =
    spectralL2SemigroupCompletion basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time
      (ContinuousMap.toLp 2 measure ℝ function) := by
  let first := (ContinuousMap.toLp 2 measure ℝ).comp
    (actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time)
  let second := (spectralL2SemigroupCompletion basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time).comp
    (ContinuousMap.toLp 2 measure ℝ)
  have equality := (actualFormContinuousEmbedding_dense_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain).equalizer
    first.continuous second.continuous (by
      funext potential
      change ContinuousMap.toLp 2 measure ℝ
        (actualFellerSemigroupCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time
          (actualFormContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential)) = _
      rw [actualFellerSemigroup_energy_calibration_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain]
      exact congrArg (fun operator => operator potential)
        (actualFormContinuousSemigroup_toLp_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time))
  exact congrFun equality function

end
end IGSIII34.Spectral



