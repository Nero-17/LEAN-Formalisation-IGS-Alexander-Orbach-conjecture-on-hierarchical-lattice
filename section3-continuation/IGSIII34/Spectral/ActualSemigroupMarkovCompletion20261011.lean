import IGSIII34.Spectral.ActualResolventMarkovCompletion20261011
import IGSIII34.Spectral.ActualEigenbasisCompletion20261011
import IGSIII34.Spectral.ResolventEulerIdentificationCompletion20261011

/-! The spectral semigroup of the actual compact form is positive and
conservative. Euler approximants are proved to be powers of its true
Lax-Milgram resolvent, rather than assumed to preserve order. -/
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

local instance ActualSemigroupMarkovCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualSemigroupMarkovCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualSemigroupMarkovCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualSemigroupMarkovCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualSemigroupMarkovCompletion20261011Complete :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

variable {Index : Type*} (basis : HilbertBasis Index ℝ (Lp ℝ 2 measure)) (eigenvalues : Index → ℝ)
  (eigenvaluesPositive : ∀ index, 0 < eigenvalues index)
  (eigenvectors : ∀ index, actualL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (basis index) = eigenvalues index • basis index)
  (generatorNonnegative : ∀ index, 0 ≤ (eigenvalues index)⁻¹-1)

include eigenvaluesPositive eigenvectors in
theorem actual_spectral_semigroup_positive_completion20261011 [measure.IsOpenPosMeasure]
    (time : ℝ≥0) (forcing : Lp ℝ 2 measure) (forcingNonnegative : 0 ≤ forcing) :
    0 ≤ spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time forcing := by
  by_cases timePositive : 0 < (time : ℝ)
  · have convergence := eulerSpectralSemigroup_strong_tendsto_completion20261011 basis
      (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time forcing
    apply ge_of_tendsto convergence
    obtain ⟨start, startAbove⟩ := exists_nat_gt (time : ℝ)
    filter_upwards [eventually_ge_atTop start] with steps stepsAbove
    have stepsPositiveReal : 0 < (steps : ℝ) := lt_of_lt_of_le (timePositive.trans startAbove) (Nat.cast_le.mpr stepsAbove)
    have timeBelowSteps : (time : ℝ) ≤ (steps : ℝ) := startAbove.le.trans (Nat.cast_le.mpr stepsAbove)
    rw [← parameter_resolvent_power_eq_euler_completion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time timePositive steps (Nat.cast_pos.mp stepsPositiveReal) timeBelowSteps]
    exact continuousLinearMap_power_positive_completion20261011 _
      (actual_normalized_parameter_resolvent_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        ((steps : ℝ)/(time : ℝ)) ((one_le_div timePositive).mpr timeBelowSteps)) forcing forcingNonnegative steps
  · have timeZero : time = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt timePositive) time.property)
    rw [timeZero, spectralL2Semigroup_zero_completion20261011]
    exact forcingNonnegative

include eigenvaluesPositive eigenvectors in
theorem actual_spectral_semigroup_constant_completion20261011
    (time : ℝ≥0) (constant : ℝ) :
    spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)) =
    actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
  by_cases timePositive : 0 < (time : ℝ)
  · let constantL2 := actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)
    have convergence := eulerSpectralSemigroup_strong_tendsto_completion20261011 basis
      (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time constantL2
    have eventuallyFixed : ∀ᶠ steps in atTop,
        eulerSpectralSemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time steps constantL2 = constantL2 := by
      obtain ⟨start, startAbove⟩ := exists_nat_gt (time : ℝ)
      filter_upwards [eventually_ge_atTop start] with steps stepsAbove
      have stepsPositiveReal : 0 < (steps : ℝ) := lt_of_lt_of_le (timePositive.trans startAbove) (Nat.cast_le.mpr stepsAbove)
      have timeBelowSteps : (time : ℝ) ≤ (steps : ℝ) := startAbove.le.trans (Nat.cast_le.mpr stepsAbove)
      rw [← parameter_resolvent_power_eq_euler_completion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
        (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time timePositive steps (Nat.cast_pos.mp stepsPositiveReal) timeBelowSteps]
      exact continuousLinearMap_power_fixed_completion20261011 _ constantL2
        (actual_normalized_parameter_resolvent_constant_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          ((steps : ℝ)/(time : ℝ)) ((one_le_div timePositive).mpr timeBelowSteps) constant) steps
    exact tendsto_nhds_unique (convergence.congr' eventuallyFixed) tendsto_const_nhds
  · have timeZero : time = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt timePositive) time.property)
    rw [timeZero, spectralL2Semigroup_zero_completion20261011]

include eigenvaluesPositive eigenvectors in
theorem actual_spectral_semigroup_interval_completion20261011 [measure.IsOpenPosMeasure]
    (time : ℝ≥0) (constant : ℝ) (forcing : Lp ℝ 2 measure) (forcingNonnegative : 0 ≤ forcing)
    (forcingUpper : forcing ≤ actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)) :
    0 ≤ spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time forcing ∧
    spectralL2SemigroupCompletion20261011 basis (fun index => (eigenvalues index)⁻¹-1) generatorNonnegative time forcing ≤
      actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
  refine ⟨actual_spectral_semigroup_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time forcing forcingNonnegative, ?_⟩
  have differenceNonnegative := actual_spectral_semigroup_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time _ (sub_nonneg.mpr forcingUpper)
  rw [map_sub, actual_spectral_semigroup_constant_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time constant] at differenceNonnegative
  exact sub_nonneg.mp differenceNonnegative

end
end IGSIII34.Spectral


