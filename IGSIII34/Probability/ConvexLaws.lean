import IGSIII34.Probability.WeakEmbedding

set_option autoImplicit false

namespace IGSIII34.Probability
noncomputable section
open MeasureTheory BoundedContinuousFunction _root_.Topology
open scoped NNReal ENNReal

variable {Outcome : Type*} [TopologicalSpace Outcome] [MeasurableSpace Outcome]
  [BorelSpace Outcome] [HasOuterApproxClosed Outcome]

def probabilityMixture (first second : ProbabilityMeasure Outcome)
    (firstWeight secondWeight : ℝ≥0) (weightsSum : firstWeight + secondWeight = 1) :
    ProbabilityMeasure Outcome :=
  ⟨firstWeight • (first : Measure Outcome) + secondWeight • (second : Measure Outcome), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, ENNReal.smul_one]
    exact_mod_cast weightsSum⟩

theorem integral_probabilityMixture (first second : ProbabilityMeasure Outcome)
    (firstWeight secondWeight : ℝ≥0) (weightsSum : firstWeight + secondWeight = 1)
    (test : Outcome →ᵇ ℝ) :
    (∫ outcome, test outcome ∂(probabilityMixture first second firstWeight secondWeight weightsSum : Measure Outcome)) =
      (firstWeight : ℝ) * (∫ outcome, test outcome ∂(first : Measure Outcome)) +
      (secondWeight : ℝ) * (∫ outcome, test outcome ∂(second : Measure Outcome)) := by
  change (∫ outcome, test outcome ∂(firstWeight • (first : Measure Outcome) +
    secondWeight • (second : Measure Outcome))) = _
  rw [integral_add_measure (test.integrable (firstWeight • (first : Measure Outcome)))
    (test.integrable (secondWeight • (second : Measure Outcome))),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  rfl

theorem integralEmbedding_mixture (first second : ProbabilityMeasure Outcome)
    (firstWeight secondWeight : ℝ≥0) (weightsSum : firstWeight + secondWeight = 1) :
    integralEmbedding (probabilityMixture first second firstWeight secondWeight weightsSum) =
      (firstWeight : ℝ) • integralEmbedding first + (secondWeight : ℝ) • integralEmbedding second := by
  funext test
  exact integral_probabilityMixture first second firstWeight secondWeight weightsSum test

theorem integralEmbedding_image_convex (family : Set (ProbabilityMeasure Outcome))
    (mixtureClosed : ∀ first ∈ family, ∀ second ∈ family,
      ∀ firstWeight secondWeight : ℝ≥0, ∀ weightsSum : firstWeight + secondWeight = 1,
        probabilityMixture first second firstWeight secondWeight weightsSum ∈ family) :
    Convex ℝ (integralEmbedding '' family) := by
  rintro _ ⟨first, firstMember, rfl⟩ _ ⟨second, secondMember, rfl⟩
    firstWeight secondWeight firstNonnegative secondNonnegative weightsSum
  let firstNNWeight : ℝ≥0 := ⟨firstWeight, firstNonnegative⟩
  let secondNNWeight : ℝ≥0 := ⟨secondWeight, secondNonnegative⟩
  have nnWeightsSum : firstNNWeight + secondNNWeight = 1 := by
    apply Subtype.ext
    exact weightsSum
  refine ⟨probabilityMixture first second firstNNWeight secondNNWeight nnWeightsSum,
    mixtureClosed first firstMember second secondMember firstNNWeight secondNNWeight nnWeightsSum, ?_⟩
  exact integralEmbedding_mixture first second firstNNWeight secondNNWeight nnWeightsSum

theorem probability_schauder_fixed_point (family : Set (ProbabilityMeasure Outcome))
    (familyCompact : IsCompact family) (familyNonempty : family.Nonempty)
    (mixtureClosed : ∀ first ∈ family, ∀ second ∈ family,
      ∀ firstWeight secondWeight : ℝ≥0, ∀ weightsSum : firstWeight + secondWeight = 1,
        probabilityMixture first second firstWeight secondWeight weightsSum ∈ family)
    (map : C(family, family)) : ∃ law, map law = law := by
  letI : CompactSpace family := isCompact_iff_compactSpace.mp familyCompact
  let represented : family → ((Outcome →ᵇ ℝ) → ℝ) :=
    fun law => integralEmbedding law.val
  have representedEmbedding : IsEmbedding represented :=
    integralEmbedding_isEmbedding.comp IsEmbedding.subtypeVal
  let homeomorphism : family ≃ₜ Set.range represented := representedEmbedding.toHomeomorph
  have rangeEquality : Set.range represented = integralEmbedding '' family := by
    ext value
    constructor
    · rintro ⟨law, rfl⟩
      exact ⟨law.val, law.property, rfl⟩
    · rintro ⟨law, membership, rfl⟩
      exact ⟨⟨law, membership⟩, rfl⟩
  have rangeConvex : Convex ℝ (Set.range represented) := by
    rw [rangeEquality]
    exact integralEmbedding_image_convex family mixtureClosed
  have rangeCompact : IsCompact (Set.range represented) :=
    isCompact_range representedEmbedding.continuous
  have rangeNonempty : (Set.range represented).Nonempty := by
    obtain ⟨law, membership⟩ := familyNonempty
    exact ⟨represented ⟨law, membership⟩, ⟨⟨law, membership⟩, rfl⟩⟩
  let conjugate : C(Set.range represented, Set.range represented) :=
    (toContinuousMap homeomorphism).comp (map.comp (toContinuousMap homeomorphism.symm))
  obtain ⟨value, fixed⟩ := IGSIII34.Topology.schauder_fixed_point
    rangeConvex rangeCompact rangeNonempty conjugate
  refine ⟨homeomorphism.symm value, homeomorphism.injective ?_⟩
  change homeomorphism (map (homeomorphism.symm value)) = value at fixed
  simpa only [Homeomorph.apply_symm_apply] using fixed

end
end IGSIII34.Probability
