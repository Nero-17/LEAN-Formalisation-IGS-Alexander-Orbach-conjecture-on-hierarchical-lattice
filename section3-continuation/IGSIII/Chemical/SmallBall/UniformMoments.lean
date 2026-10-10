import IGSIII.Chemical.SmallBall.InverseMoments

/-! Explicit moment bounds depending only on a common geometric tail bound.
This supplies uniform moment control for a family of laws. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

variable {Sample : Type*} [MeasurableSpace Sample]

/-- An elementary Paley--Zygmund bound at one half.  The proof integrates a
quadratic majorant, so no independence or distributional assumption is needed. -/
theorem smallBall_half_le_of_mean_one_second_moment_bound
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} {bound : ℝ}
    (measurable : Measurable value) (integrable : Integrable value measure)
    (squareIntegrable : Integrable (fun sample => value sample ^ 2) measure)
    (meanOne : (∫ sample, value sample ∂measure) = 1)
    (boundPositive : 0 < bound)
    (secondMomentBound : (∫ sample, value sample ^ 2 ∂measure) ≤ bound) :
    measure.real {sample | value sample ≤ (1 / 2 : ℝ)} ≤ 1 - 1 / (4 * bound) := by
  have measurableEvent : MeasurableSet {sample | value sample ≤ (1 / 2 : ℝ)} :=
    measurableSet_le measurable measurable_const
  have indicatorIntegrable : Integrable
      ({sample | value sample ≤ (1 / 2 : ℝ)}ᶜ.indicator (fun _ => bound)) measure :=
    (integrable_const bound).indicator measurableEvent.compl
  have quadraticIntegrable : Integrable
      (fun sample => (1 / 2 : ℝ) + value sample ^ 2 / (4 * bound)) measure :=
    (integrable_const (1 / 2 : ℝ)).add (squareIntegrable.div_const (4 * bound))
  have comparison := integral_mono integrable
    (quadraticIntegrable.add indicatorIntegrable) (fun sample => by
      change value sample ≤ (1 / 2 : ℝ) + value sample ^ 2 / (4 * bound) +
        {sample | value sample ≤ (1 / 2 : ℝ)}ᶜ.indicator (fun _ => bound) sample
      by_cases small : value sample ≤ (1 / 2 : ℝ)
      · rw [Set.indicator_of_notMem
          (show sample ∉ {sample | value sample ≤ (1 / 2 : ℝ)}ᶜ by simpa using small), add_zero]
        exact small.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity)))
      · rw [Set.indicator_of_mem
          (show sample ∈ {sample | value sample ≤ (1 / 2 : ℝ)}ᶜ from small)]
        have divisionIdentity : value sample ^ 2 / (4 * bound) * (4 * bound) =
            value sample ^ 2 := div_mul_cancel₀ _ (by positivity)
        nlinarith [sq_nonneg (value sample - 2 * bound)])
  change (∫ sample, value sample ∂measure) ≤
    (∫ sample, ((1 / 2 : ℝ) + value sample ^ 2 / (4 * bound)) +
      {sample | value sample ≤ (1 / 2 : ℝ)}ᶜ.indicator (fun _ => bound) sample ∂measure)
    at comparison
  rw [meanOne, integral_add quadraticIntegrable indicatorIntegrable,
    integral_add (integrable_const _) (squareIntegrable.div_const _), integral_const,
    probReal_univ, smul_eq_mul, one_mul, integral_div,
    integral_indicator_const _ measurableEvent.compl, smul_eq_mul,
    measureReal_compl measurableEvent, probReal_univ] at comparison
  have dividedBound : (∫ sample, value sample ^ 2 ∂measure) / (4 * bound) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * bound)).mpr
    nlinarith
  apply (le_sub_iff_add_le).mpr
  have reciprocalIdentity : 1 / (4 * bound) * (4 * bound) = 1 :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

theorem exists_uniform_smallBall_start_of_second_moment_bound {Index : Type*}
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) {bound : ℝ}
    (measurable : ∀ index, Measurable (value index))
    (integrable : ∀ index, Integrable (value index) measure)
    (squareIntegrable : ∀ index, Integrable (fun sample => value index sample ^ 2) measure)
    (meanOne : ∀ index, (∫ sample, value index sample ∂measure) = 1)
    (boundAtLeastOne : 1 ≤ bound)
    (secondMomentBound : ∀ index, (∫ sample, value index sample ^ 2 ∂measure) ≤ bound) :
    ∃ start : ℝ, 0 ≤ start ∧ start < 1 ∧
      ∀ index, measure.real {sample | value index sample ≤ (1 / 2 : ℝ)} ≤ start := by
  have boundPositive : 0 < bound := zero_lt_one.trans_le boundAtLeastOne
  refine ⟨1 - 1 / (4 * bound), ?_, ?_, ?_⟩
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * bound)).mpr
    linarith
  · exact sub_lt_self _ (by positivity)
  · intro index
    exact smallBall_half_le_of_mean_one_second_moment_bound measure (measurable index)
      (integrable index) (squareIntegrable index) (meanOne index) boundPositive
      (secondMomentBound index)

/-- A natural moment above a real order controls that real moment with an
explicit additive constant. -/
theorem integral_rpow_le_one_add_integral_pow
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} (measurable : Measurable value)
    (nonnegative : ∀ sample, 0 ≤ value sample) {exponent : ℝ} {power : ℕ}
    (exponentNonnegative : 0 ≤ exponent) (exponentBound : exponent ≤ power)
    (powerIntegrable : Integrable (fun sample => value sample ^ power) measure) :
    (∫ sample, value sample ^ exponent ∂measure) ≤
      1 + (∫ sample, value sample ^ power ∂measure) := by
  have comparison (sample : Sample) : value sample ^ exponent ≤ 1 + value sample ^ power := by
    by_cases belowOne : value sample ≤ 1
    · have bounded := Real.rpow_le_rpow (nonnegative sample) belowOne exponentNonnegative
      simp only [Real.one_rpow] at bounded
      exact bounded.trans (le_add_of_nonneg_right (pow_nonneg (nonnegative sample) power))
    · have bounded := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge belowOne) exponentBound
      rw [Real.rpow_natCast] at bounded
      exact bounded.trans (le_add_of_nonneg_left zero_le_one)
  have realIntegrable : Integrable (fun sample => value sample ^ exponent) measure := by
    apply ((integrable_const (1 : ℝ)).add powerIntegrable).mono'
      ((Real.continuous_rpow_const exponentNonnegative).measurable.comp measurable).aestronglyMeasurable
    filter_upwards with sample
    change ‖value sample ^ exponent‖ ≤ 1 + value sample ^ power
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (nonnegative sample) exponent)]
    exact comparison sample
  have integralComparison := integral_mono realIntegrable
    ((integrable_const (1 : ℝ)).add powerIntegrable) comparison
  change (∫ sample, value sample ^ exponent ∂measure) ≤
    (∫ sample, 1 + value sample ^ power ∂measure) at integralComparison
  simpa only [integral_add (integrable_const _) powerIntegrable,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using integralComparison

theorem exists_uniform_real_inverse_moment_bound_of_natural_bounds {Index : Type*}
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (measurable : ∀ index, Measurable (value index))
    (positive : ∀ index sample, 0 < value index sample)
    (inverseIntegrable : ∀ index power, Integrable (fun sample => (value index sample)⁻¹ ^ power) measure)
    (naturalBounds : ∀ power : ℕ, ∃ bound : ℝ, ∀ index,
      (∫ sample, (value index sample)⁻¹ ^ power ∂measure) ≤ bound)
    {exponent : ℝ} (exponentNonnegative : 0 ≤ exponent) :
    ∃ bound : ℝ, ∀ index, (∫ sample, value index sample ^ (-exponent) ∂measure) ≤ bound := by
  obtain ⟨power, exponentBound⟩ := exists_nat_ge exponent
  obtain ⟨bound, naturalBound⟩ := naturalBounds power
  refine ⟨1 + bound, ?_⟩
  intro index
  have comparison := integral_rpow_le_one_add_integral_pow measure (measurable index).inv
    (fun sample => (inv_pos.mpr (positive index sample)).le) exponentNonnegative exponentBound
    (inverseIntegrable index power)
  simp only [Pi.inv_apply] at comparison
  simp only [Real.rpow_neg_eq_inv_rpow] at ⊢
  have naturalBoundAtIndex := naturalBound index
  linarith

theorem geometricShell_pairwiseDisjoint {value : Sample → ℝ} {base : ℝ}
    (baseAboveOne : 1 < base) :
    Pairwise (fun first second => Disjoint (geometricShell value base first)
      (geometricShell value base second)) := by
  intro first second different
  apply Set.disjoint_left.mpr
  intro sample firstWithin secondWithin
  rcases lt_or_gt_of_ne different with less | greater
  · have ordered := pow_le_pow_right₀ baseAboveOne.le (Nat.succ_le_of_lt less)
    exact (not_lt_of_ge secondWithin.1) (firstWithin.2.trans_le ordered)
  · have ordered := pow_le_pow_right₀ baseAboveOne.le (Nat.succ_le_of_lt greater)
    exact (not_lt_of_ge firstWithin.1) (secondWithin.2.trans_le ordered)

theorem geometricShell_disjoint_small {value : Sample → ℝ} {base : ℝ}
    (baseAboveOne : 1 < base) :
    Disjoint {sample | value sample < 1} (⋃ depth : ℕ, geometricShell value base depth) := by
  apply disjoint_iUnion_right.mpr
  intro depth
  apply Set.disjoint_left.mpr
  intro sample belowOne within
  exact (not_le_of_gt belowOne) ((one_le_pow₀ baseAboveOne.le).trans within.1)

theorem integral_pow_le_of_geometric_tail_bound (measure : Measure Sample)
    [IsFiniteMeasure measure] {value : Sample → ℝ} {base : ℝ} (power : ℕ)
    (measurable : Measurable value) (nonnegative : ∀ sample, 0 ≤ value sample)
    (baseAboveOne : 1 < base) {weightedBound : ℕ → ℝ}
    (boundSummable : Summable weightedBound)
    (tailBound : ∀ depth : ℕ,
      (base ^ power) ^ depth * measure.real {sample | base ^ depth ≤ value sample} ≤
        weightedBound depth) :
    (∫ sample, value sample ^ power ∂measure) ≤
      measure.real univ + base ^ power * ∑' depth : ℕ, weightedBound depth := by
  have baseNonnegative : 0 ≤ base := (zero_lt_one.trans baseAboveOne).le
  have tailSummable : Summable (fun depth : ℕ =>
      (base ^ power) ^ depth * measure.real {sample | base ^ depth ≤ value sample}) :=
    Summable.of_nonneg_of_le (fun depth => mul_nonneg
      (pow_nonneg (pow_nonneg baseNonnegative power) depth) measureReal_nonneg) tailBound boundSummable
  have integrable := integrable_pow_of_summable_geometric_tails measure power measurable
    nonnegative baseAboveOne tailSummable
  have shellIntegralBound (depth : ℕ) :
      (∫ sample in geometricShell value base depth, value sample ^ power ∂measure) ≤
        base ^ power * weightedBound depth := by
    have bounded := norm_setIntegral_le_of_norm_le_const
      (f := fun sample => value sample ^ power)
      (measure_lt_top measure (geometricShell value base depth))
      (fun sample within => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (nonnegative sample) power)]
        exact pow_le_pow_left₀ (nonnegative sample) within.2.le power)
    calc
      (∫ sample in geometricShell value base depth, value sample ^ power ∂measure) ≤
          ‖∫ sample in geometricShell value base depth, value sample ^ power ∂measure‖ :=
        le_abs_self _
      _ ≤ (base ^ (depth + 1)) ^ power *
          measure.real (geometricShell value base depth) := bounded
      _ ≤ (base ^ (depth + 1)) ^ power *
          measure.real {sample | base ^ depth ≤ value sample} :=
        mul_le_mul_of_nonneg_left (measureReal_mono (fun _ within => within.1))
          (pow_nonneg (pow_nonneg baseNonnegative _) _)
      _ = base ^ power * ((base ^ power) ^ depth *
          measure.real {sample | base ^ depth ≤ value sample}) := by
        rw [← pow_mul, Nat.mul_comm (depth + 1) power, pow_mul, pow_succ]
        ring
      _ ≤ base ^ power * weightedBound depth :=
        mul_le_mul_of_nonneg_left (tailBound depth) (pow_nonneg baseNonnegative power)
  have smallIntegralBound :
      (∫ sample in {sample | value sample < 1}, value sample ^ power ∂measure) ≤
        measure.real univ := by
    have bounded := norm_setIntegral_le_of_norm_le_const
      (f := fun sample => value sample ^ power)
      (measure_lt_top measure {sample | value sample < 1})
      (C := 1) (fun sample within => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (nonnegative sample) power)]
        exact (pow_le_pow_left₀ (nonnegative sample) within.le power).trans_eq (one_pow power))
    have bounded' :
        ‖∫ sample in {sample | value sample < 1}, value sample ^ power ∂measure‖ ≤
          measure.real {sample | value sample < 1} := by
      simpa only [one_mul] using bounded
    exact (le_abs_self _).trans (bounded'.trans (measureReal_mono (subset_univ _)))
  have shellSum := hasSum_integral_iUnion
    (geometricShell_measurable measurable base)
    (geometricShell_pairwiseDisjoint baseAboveOne)
    (integrable.integrableOn (s := ⋃ depth : ℕ, geometricShell value base depth))
  have shellIntegralSumBound :
      (∫ sample in ⋃ depth : ℕ, geometricShell value base depth, value sample ^ power ∂measure) ≤
        base ^ power * ∑' depth : ℕ, weightedBound depth := by
    rw [← shellSum.tsum_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum shellIntegralBound shellSum.summable
      (boundSummable.mul_left (base ^ power))
  have decomposition := setIntegral_union (f := fun sample => value sample ^ power)
    (geometricShell_disjoint_small baseAboveOne)
    (MeasurableSet.iUnion (geometricShell_measurable measurable base))
    integrable.integrableOn integrable.integrableOn
  simp only [geometricShell_cover baseAboveOne, Measure.restrict_univ] at decomposition
  rw [decomposition]
  exact add_le_add smallIntegralBound shellIntegralSumBound

theorem integral_inv_pow_le_of_smallBall_bound (measure : Measure Sample)
    [IsFiniteMeasure measure] {value : Sample → ℝ} {base cutoff : ℝ} (power : ℕ)
    (measurable : Measurable value) (positive : ∀ sample, 0 < value sample)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff) {weightedBound : ℕ → ℝ}
    (boundSummable : Summable weightedBound)
    (tailBound : ∀ depth : ℕ,
      (base ^ power) ^ depth * measure.real {sample | value sample ≤ cutoff / base ^ depth} ≤
        weightedBound depth) :
    (∫ sample, (value sample)⁻¹ ^ power ∂measure) ≤
      cutoff⁻¹ ^ power *
        (measure.real univ + base ^ power * ∑' depth : ℕ, weightedBound depth) := by
  have events (depth : ℕ) :
      {sample | base ^ depth ≤ cutoff / value sample} =
        {sample | value sample ≤ cutoff / base ^ depth} := by
    ext sample
    simp only [mem_setOf_eq, le_div_iff₀ (positive sample),
      le_div_iff₀ (pow_pos (zero_lt_one.trans baseAboveOne) depth), mul_comm]
  have scaledBound := integral_pow_le_of_geometric_tail_bound measure power
    (measurable_const.div measurable)
    (fun sample => (div_pos cutoffPositive (positive sample)).le) baseAboveOne boundSummable
    (by simpa only [Pi.div_apply, events] using tailBound)
  have rescale : (fun sample => (value sample)⁻¹ ^ power) =
      (fun sample => cutoff⁻¹ ^ power * (cutoff / value sample) ^ power) := by
    funext sample
    rw [← mul_pow]
    congr 1
    field_simp
  rw [rescale, integral_const_mul]
  exact mul_le_mul_of_nonneg_left scaledBound (pow_nonneg (inv_pos.mpr cutoffPositive).le power)

/-- The displayed constant does not depend on the law beyond its common tail
bound. Hence it gives uniform inverse moments when applied to a family. -/
theorem integral_inv_pow_le_of_thinning_tail_bound
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} {critical start base cutoff : ℝ} (power : ℕ)
    (measurable : Measurable value) (positive : ∀ sample, 0 < value sample)
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (tailBound : ∀ depth : ℕ,
      measure.real {sample | value sample ≤ cutoff / base ^ depth} ≤
        (thinningMap network critical)^[depth] start) :
    (∫ sample, (value sample)⁻¹ ^ power ∂measure) ≤
      cutoff⁻¹ ^ power * (1 + base ^ power *
        ∑' depth : ℕ, (base ^ power) ^ depth * (thinningMap network critical)^[depth] start) := by
  have summability := thinningMap_weighted_iterate_summable network criticalPositive
    criticalBelowOne fixedPoint scale startNonnegative startBelowOne
    (pow_pos (zero_lt_one.trans baseAboveOne) power)
  simpa only [probReal_univ] using integral_inv_pow_le_of_smallBall_bound measure power
    measurable positive baseAboveOne cutoffPositive summability
    (fun depth => mul_le_mul_of_nonneg_left (tailBound depth)
      (pow_nonneg (pow_nonneg (zero_lt_one.trans baseAboveOne).le power) depth))

end
end IGSIII.Chemical.SmallBall
