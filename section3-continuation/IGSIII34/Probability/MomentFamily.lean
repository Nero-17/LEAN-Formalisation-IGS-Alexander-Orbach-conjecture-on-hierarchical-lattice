import IGSIII34.Probability.MeanContinuity
import IGSIII34.Percolation.LawMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Set _root_.Topology
open scoped NNReal ENNReal

theorem lintegral_eq_one_of_mean_eq_one (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1) :
    (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1 := by
  have integrable : Integrable (fun value : ℝ≥0 => (value : ℝ)) (law : Measure ℝ≥0) :=
    Integrable.of_integral_ne_zero (by rw [meanOne]; exact one_ne_zero)
  rw [lintegral_coe_eq_integral (fun value : ℝ≥0 => value) integrable, meanOne]
  exact ENNReal.ofReal_one

theorem mean_eq_one_of_lintegral_eq_one (law : ProbabilityMeasure ℝ≥0)
    (meanOne : (∫⁻ value, (value : ℝ≥0∞) ∂(law : Measure ℝ≥0)) = 1) :
    (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1 := by
  have equality := integral_toReal (μ := (law : Measure ℝ≥0))
    (f := fun value : ℝ≥0 => (value : ℝ≥0∞)) measurable_id.coe_nnreal_ennreal.aemeasurable
    (ae_of_all _ (fun value : ℝ≥0 => ENNReal.coe_lt_top))
  simpa only [ENNReal.coe_toReal, meanOne, ENNReal.toReal_one] using equality

theorem moment_le_one_add_higherMoment (law : ProbabilityMeasure ℝ≥0)
    {power higherOrder : ℕ} (orderBound : power ≤ higherOrder) :
    (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤
      1 + ∫⁻ value, (value : ℝ≥0∞) ^ higherOrder ∂(law : Measure ℝ≥0) := by
  calc
    _ ≤ ∫⁻ value, 1 + (value : ℝ≥0∞) ^ higherOrder ∂(law : Measure ℝ≥0) := by
      apply lintegral_mono
      intro value
      by_cases below : (value : ℝ≥0∞) ≤ 1
      · have momentBelow : (value : ℝ≥0∞) ^ power ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left' below power
        exact momentBelow.trans (le_add_of_nonneg_right zero_le)
      · exact (pow_le_pow_right' (le_of_not_ge below) orderBound).trans
          (le_add_of_nonneg_left zero_le)
    _ = _ := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]

theorem secondMoment_le_one_add_higherMoment (law : ProbabilityMeasure ℝ≥0)
    {power : ℕ} (powerAtLeastTwo : 2 ≤ power) :
    (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤
      1 + ∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0) := by
  calc
    _ ≤ ∫⁻ value, 1 + (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0) := by
      apply lintegral_mono
      intro value
      by_cases below : (value : ℝ≥0∞) ≤ 1
      · have squareBelow : (value : ℝ≥0∞) ^ 2 ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left' below 2
        exact squareBelow.trans (le_add_of_nonneg_right zero_le)
      · exact (pow_le_pow_right' (le_of_not_ge below) powerAtLeastTwo).trans (le_add_of_nonneg_left zero_le)
    _ = _ := by rw [lintegral_add_left measurable_const]; simp only [lintegral_const, measure_univ, mul_one]

def meanOneMomentFamily (lowerOrder : ℕ) (bounds : ℕ → ℝ≥0) : Set (ProbabilityMeasure ℝ≥0) :=
  {law | (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1 ∧
    ∀ power : ℕ, lowerOrder ≤ power →
      (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤ bounds power}

theorem meanOneMomentFamily_secondMoment_bound (lowerOrder : ℕ) (bounds : ℕ → ℝ≥0)
    (lowerOrderAtLeastTwo : 2 ≤ lowerOrder) (law : ProbabilityMeasure ℝ≥0)
    (member : law ∈ meanOneMomentFamily lowerOrder bounds) :
    (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ (1 + bounds lowerOrder : ℝ≥0) :=
  (secondMoment_le_one_add_higherMoment law lowerOrderAtLeastTwo).trans
    (by simpa only [ENNReal.coe_add, ENNReal.coe_one] using add_le_add le_rfl (member.2 lowerOrder le_rfl))

theorem isClosed_naturalMoment_sublevel (power : ℕ) (bound : ℝ≥0) :
    IsClosed {law : ProbabilityMeasure ℝ≥0 |
      (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) ≤ bound} := by
  convert isClosed_lintegral_sublevel (fun value : ℝ≥0 => value ^ power)
    (continuous_id.pow power) bound using 1
  ext law
  simp only [Set.mem_setOf_eq]
  have equality : (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) =
      ∫⁻ value : ℝ≥0, ((value ^ power : ℝ≥0) : ℝ≥0∞) ∂(law : Measure ℝ≥0) :=
    lintegral_congr (fun value => (ENNReal.coe_pow value power).symm)
  rw [equality]

theorem isCompact_meanOneMomentFamily (lowerOrder : ℕ) (bounds : ℕ → ℝ≥0)
    (lowerOrderAtLeastTwo : 2 ≤ lowerOrder) :
    IsCompact (meanOneMomentFamily lowerOrder bounds) := by
  let domain := {law : ProbabilityMeasure ℝ≥0 |
    (∫⁻ value, (value : ℝ≥0∞) ^ 2 ∂(law : Measure ℝ≥0)) ≤ (1 + bounds lowerOrder : ℝ≥0) ∧
    (∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0)) = 1}
  letI : CompactSpace domain := isCompact_iff_compactSpace.mp
    (isCompact_meanOne_secondMoment_sublevel (1 + bounds lowerOrder))
  have closed : IsClosed {law : domain | ∀ power : ℕ, lowerOrder ≤ power →
      (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law.val : Measure ℝ≥0)) ≤ bounds power} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro power
    apply isClosed_iInter
    intro _
    exact (isClosed_naturalMoment_sublevel power (bounds power)).preimage continuous_subtype_val
  have compactImage := closed.isCompact.image
    (continuous_subtype_val : Continuous (Subtype.val : domain → ProbabilityMeasure ℝ≥0))
  convert compactImage using 1
  ext law
  constructor
  · intro member
    exact ⟨⟨law, meanOneMomentFamily_secondMoment_bound lowerOrder bounds lowerOrderAtLeastTwo law member,
      member.1⟩, member.2, rfl⟩
  · rintro ⟨member, boundsHold, rfl⟩
    exact ⟨member.property.2, boundsHold⟩

theorem meanOneMomentFamily_nonempty (lowerOrder : ℕ) (bounds : ℕ → ℝ≥0)
    (boundsAtLeastOne : ∀ power, lowerOrder ≤ power → 1 ≤ bounds power) :
    (meanOneMomentFamily lowerOrder bounds).Nonempty := by
  refine ⟨MeasureTheory.diracProba (1 : ℝ≥0), ?_, ?_⟩
  · change (∫ value : ℝ≥0, (value : ℝ) ∂Measure.dirac (1 : ℝ≥0)) = 1
    simp
  · intro power orderBound
    change (∫⁻ value : ℝ≥0, (value : ℝ≥0∞) ^ power ∂Measure.dirac (1 : ℝ≥0)) ≤ bounds power
    simpa only [lintegral_dirac, ENNReal.coe_one, one_pow] using
      ENNReal.coe_le_coe.mpr (boundsAtLeastOne power orderBound)

theorem meanOneMomentFamily_mixture_closed (lowerOrder : ℕ) (bounds : ℕ → ℝ≥0)
    (first second : ProbabilityMeasure ℝ≥0)
    (firstMember : first ∈ meanOneMomentFamily lowerOrder bounds)
    (secondMember : second ∈ meanOneMomentFamily lowerOrder bounds)
    (firstWeight secondWeight : ℝ≥0) (weightsSum : firstWeight + secondWeight = 1) :
    probabilityMixture first second firstWeight secondWeight weightsSum ∈
      meanOneMomentFamily lowerOrder bounds := by
  constructor
  · apply mean_eq_one_of_lintegral_eq_one
    rw [lintegral_probabilityMixture, lintegral_eq_one_of_mean_eq_one first firstMember.1,
      lintegral_eq_one_of_mean_eq_one second secondMember.1, mul_one, mul_one,
      ← ENNReal.coe_add, weightsSum, ENNReal.coe_one]
  · intro power orderBound
    exact probabilityMixture_lintegral_le first second firstWeight secondWeight weightsSum
      (fun value : ℝ≥0 => (value : ℝ≥0∞) ^ power)
      (firstMember.2 power orderBound) (secondMember.2 power orderBound)

theorem meanOneMomentFamily_all_moments_finite (lowerOrder : ℕ) (bounds : ℕ → ℝ≥0)
    (law : ProbabilityMeasure ℝ≥0) (member : law ∈ meanOneMomentFamily lowerOrder bounds)
    (power : ℕ) :
    (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0)) < ∞ := by
  have orderBound : power ≤ max lowerOrder power := le_max_right _ _
  have largeMoment := member.2 (max lowerOrder power) (le_max_left _ _)
  have finite : (1 : ℝ≥0∞) + bounds (max lowerOrder power) < ∞ := by simp
  exact ((moment_le_one_add_higherMoment law orderBound).trans
    (add_le_add le_rfl largeMoment)).trans_lt finite


end
end IGSIII34.Probability


