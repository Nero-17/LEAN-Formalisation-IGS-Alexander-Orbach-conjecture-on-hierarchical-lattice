import IGSIII34.Spectral.ActualFellerSemigroupCompletion20261011

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

local instance actualFellerMarkovNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerMarkovUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualFellerMarkovTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualFellerMarkovInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualFellerMarkovCompleteCompletion20261011 :
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

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualFellerSemigroup_zero_completion20261011
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative 0 function = function := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
  rw [actualFellerSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain,
    spectralL2Semigroup_zero_completion20261011]

include denseDomain in
theorem actualFellerSemigroup_add_completion20261011
    (first second : ℝ≥0)
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative first
      (actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative second function) =
    actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative (first+second) function := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
  rw [actualFellerSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain,
    actualFellerSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain,
    actualFellerSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain,
    spectralL2Semigroup_add_completion20261011]

include denseDomain in
theorem actualFellerSemigroup_constant_completion20261011
    (time : ℝ≥0) (constant : ℝ) :
    actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time (ContinuousMap.const _ constant) =
    ContinuousMap.const _ constant := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) measure
  rw [actualFellerSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain]
  exact actual_spectral_semigroup_canonical_constant_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time constant

include denseDomain in
theorem actualFellerSemigroup_positive_completion20261011
    (time : ℝ≥0)
    (function : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (nonnegative : ∀ point, 0 ≤ function point) :
    ∀ point, 0 ≤ actualFellerSemigroupCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time function point := by
  apply continuousMap_nonnegative_of_toLp_nonnegative_completion20261011 measure
  rw [actualFellerSemigroup_toLp_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative denseDomain]
  apply actual_spectral_semigroup_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    basis eigenvalues eigenvaluesPositive eigenvectors generatorNonnegative time
  have order := (continuousMap_le_iff_toLp_le_completion20261011 measure 0 function).mp nonnegative
  simpa only [map_zero] using order

end
end IGSIII34.Spectral



