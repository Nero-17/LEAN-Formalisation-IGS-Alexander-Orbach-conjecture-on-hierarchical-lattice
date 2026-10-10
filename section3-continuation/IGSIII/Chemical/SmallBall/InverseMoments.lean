import IGSIII.Chemical.SmallBall.NetworkMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Integration of geometric tail bounds.  These lemmas prove moment integrability
from a summable tail bound; moment integrability is not an input hypothesis. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

variable {Sample : Type*} [MeasurableSpace Sample]

def geometricShell (value : Sample → ℝ) (base : ℝ) (depth : ℕ) : Set Sample :=
  {sample | base ^ depth ≤ value sample ∧ value sample < base ^ (depth + 1)}

theorem geometricShell_measurable {value : Sample → ℝ} (measurable : Measurable value)
    (base : ℝ) (depth : ℕ) : MeasurableSet (geometricShell value base depth) := by
  exact (measurableSet_le measurable_const measurable).inter
    (measurableSet_lt measurable measurable_const)

theorem geometricShell_cover {value : Sample → ℝ} {base : ℝ} (baseAboveOne : 1 < base) :
    {sample | value sample < 1} ∪ (⋃ depth : ℕ, geometricShell value base depth) = univ := by
  apply eq_univ_of_forall
  intro sample
  by_cases below : value sample < 1
  · exact Or.inl below
  · obtain ⟨depth, bounds⟩ := exists_nat_pow_near (le_of_not_gt below) baseAboveOne
    exact Or.inr (mem_iUnion.mpr ⟨depth, bounds⟩)

theorem integrable_pow_of_summable_geometric_tails (measure : Measure Sample)
    [IsFiniteMeasure measure] {value : Sample → ℝ} {base : ℝ} (power : ℕ)
    (measurable : Measurable value) (nonnegative : ∀ sample, 0 ≤ value sample)
    (baseAboveOne : 1 < base)
    (tailSummable : Summable (fun depth : ℕ =>
      (base ^ power) ^ depth * measure.real {sample | base ^ depth ≤ value sample})) :
    Integrable (fun sample => value sample ^ power) measure := by
  have baseNonnegative : 0 ≤ base := (zero_lt_one.trans baseAboveOne).le
  have shellBound (depth : ℕ) (sample : Sample)
      (within : sample ∈ geometricShell value base depth) :
      ‖value sample ^ power‖ ≤ (base ^ (depth + 1)) ^ power := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (nonnegative sample) power)]
    exact pow_le_pow_left₀ (nonnegative sample) within.2.le power
  have shellIntegrable (depth : ℕ) :
      IntegrableOn (fun sample => value sample ^ power) (geometricShell value base depth) measure := by
    apply (integrable_const ((base ^ (depth + 1)) ^ power)).mono'
      (measurable.pow_const power).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (geometricShell_measurable measurable base depth)]
      with sample within
    exact shellBound depth sample within
  have shellIntegralBound (depth : ℕ) :
      (∫ sample in geometricShell value base depth, ‖value sample ^ power‖ ∂measure) ≤
        base ^ power * ((base ^ power) ^ depth *
          measure.real {sample | base ^ depth ≤ value sample}) := by
    have bounded := norm_setIntegral_le_of_norm_le_const
      (f := fun sample => ‖value sample ^ power‖)
      (measure_lt_top measure (geometricShell value base depth))
      (fun sample within => by simpa only [norm_norm] using shellBound depth sample within)
    calc
      (∫ sample in geometricShell value base depth, ‖value sample ^ power‖ ∂measure) ≤
          ‖∫ sample in geometricShell value base depth, ‖value sample ^ power‖ ∂measure‖ :=
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
  have shellsIntegrable :
      IntegrableOn (fun sample => value sample ^ power)
        (⋃ depth : ℕ, geometricShell value base depth) measure := by
    apply integrableOn_iUnion_of_summable_integral_norm shellIntegrable
    apply Summable.of_nonneg_of_le
      (fun depth => integral_nonneg (fun sample => norm_nonneg _)) shellIntegralBound
    exact tailSummable.mul_left (base ^ power)
  have smallIntegrable :
      IntegrableOn (fun sample => value sample ^ power) {sample | value sample < 1} measure := by
    apply (integrable_const (1 : ℝ)).mono' (measurable.pow_const power).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable measurable_const)]
      with sample within
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (nonnegative sample) power)]
    exact (pow_le_pow_left₀ (nonnegative sample) within.le power).trans_eq (one_pow power)
  have integrableUnion := integrableOn_union.mpr ⟨smallIntegrable, shellsIntegrable⟩
  simpa only [geometricShell_cover baseAboveOne, integrableOn_univ] using integrableUnion

/-- The cutoff can be any positive number.  This is the integral step used after
choosing a sufficiently small initial small-ball threshold. -/
theorem integrable_inv_pow_of_summable_smallBall (measure : Measure Sample)
    [IsFiniteMeasure measure] {value : Sample → ℝ} {base cutoff : ℝ} (power : ℕ)
    (measurable : Measurable value) (positive : ∀ sample, 0 < value sample)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (tailSummable : Summable (fun depth : ℕ =>
      (base ^ power) ^ depth * measure.real {sample | value sample ≤ cutoff / base ^ depth})) :
    Integrable (fun sample => (value sample)⁻¹ ^ power) measure := by
  have events (depth : ℕ) :
      {sample | base ^ depth ≤ cutoff / value sample} =
        {sample | value sample ≤ cutoff / base ^ depth} := by
    ext sample
    simp only [mem_setOf_eq, le_div_iff₀ (positive sample),
      le_div_iff₀ (pow_pos (zero_lt_one.trans baseAboveOne) depth), mul_comm]
  have scaledIntegrable : Integrable (fun sample => (cutoff / value sample) ^ power) measure := by
    apply integrable_pow_of_summable_geometric_tails measure power
      (measurable_const.div measurable)
      (fun sample => (div_pos cutoffPositive (positive sample)).le) baseAboveOne
    simpa only [Pi.div_apply, events] using tailSummable
  have rescaled := scaledIntegrable.const_mul (cutoff⁻¹ ^ power)
  convert rescaled using 1
  funext sample
  rw [← mul_pow]
  congr 1
  field_simp

/-- An actual reliability-map tail recursion implies all natural inverse moments.
The input is a small-ball event recursion, never the desired moment conclusion. -/
theorem integrable_inv_pow_of_thinning_recursion
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} {critical start base cutoff : ℝ} (power : ℕ)
    (measurable : Measurable value) (positive : ∀ sample, 0 < value sample)
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAboveOne : 1 < base) (cutoffPositive : 0 < cutoff)
    (initial : measure.real {sample | value sample ≤ cutoff} ≤ start)
    (step : ∀ depth : ℕ,
      measure.real {sample | value sample ≤ cutoff / base ^ (depth + 1)} ≤
        thinningMap network critical
          (measure.real {sample | value sample ≤ cutoff / base ^ depth})) :
    Integrable (fun sample => (value sample)⁻¹ ^ power) measure := by
  have orbitBounds := iterate_bounds startNonnegative startBelowOne
    (thinningMap_zero network critical)
    (fun input nonnegative belowOne => thinningMap_nonnegative network criticalPositive
      criticalBelowOne nonnegative belowOne.le)
    (fun input positive belowOne => thinningMap_strict network criticalPositive criticalBelowOne
      fixedPoint scale positive belowOne)
  have tailBound : ∀ depth : ℕ,
      measure.real {sample | value sample ≤ cutoff / base ^ depth} ≤
        (thinningMap network critical)^[depth] start := by
    apply tail_le_iterate_on (thinningMap_monotoneOn network criticalPositive criticalBelowOne)
      (fun depth => ⟨(orbitBounds depth).1, (orbitBounds depth).2.trans startBelowOne.le⟩)
      (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
      (by simpa using initial) step
  apply integrable_inv_pow_of_summable_smallBall measure power measurable positive
    baseAboveOne cutoffPositive
  apply Summable.of_nonneg_of_le
    (fun depth => mul_nonneg (pow_nonneg (pow_nonneg
      (zero_lt_one.trans baseAboveOne).le power) depth) measureReal_nonneg)
    (fun depth => mul_le_mul_of_nonneg_left (tailBound depth)
      (pow_nonneg (pow_nonneg (zero_lt_one.trans baseAboveOne).le power) depth))
  exact thinningMap_weighted_iterate_summable network criticalPositive criticalBelowOne fixedPoint
    scale startNonnegative startBelowOne (pow_pos (zero_lt_one.trans baseAboveOne) power)

theorem integrable_rpow_of_nat_moments (measure : Measure Sample) [IsFiniteMeasure measure]
    {value : Sample → ℝ} (measurable : Measurable value)
    (nonnegative : ∀ sample, 0 ≤ value sample)
    (naturalMoments : ∀ power : ℕ, Integrable (fun sample => value sample ^ power) measure)
    {exponent : ℝ} (exponentNonnegative : 0 ≤ exponent) :
    Integrable (fun sample => value sample ^ exponent) measure := by
  obtain ⟨power, exponentBound⟩ := exists_nat_ge exponent
  apply ((integrable_const (1 : ℝ)).add (naturalMoments power)).mono'
    ((Real.continuous_rpow_const exponentNonnegative).measurable.comp measurable).aestronglyMeasurable
  filter_upwards with sample
  change ‖value sample ^ exponent‖ ≤ 1 + value sample ^ power
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (nonnegative sample) exponent)]
  by_cases belowOne : value sample ≤ 1
  · have bounded := Real.rpow_le_rpow (nonnegative sample) belowOne exponentNonnegative
    simp only [Real.one_rpow] at bounded
    exact bounded.trans (le_add_of_nonneg_right (pow_nonneg (nonnegative sample) power))
  · have bounded := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge belowOne) exponentBound
    rw [Real.rpow_natCast] at bounded
    exact bounded.trans (le_add_of_nonneg_left zero_le_one)

/-- All finite real inverse powers follow as well, including noninteger powers. -/
theorem integrable_negative_rpow_of_nat_inverse_moments
    (measure : Measure Sample) [IsFiniteMeasure measure]
    {value : Sample → ℝ} (measurable : Measurable value)
    (positive : ∀ sample, 0 < value sample)
    (naturalInverseMoments : ∀ power : ℕ,
      Integrable (fun sample => (value sample)⁻¹ ^ power) measure)
    {exponent : ℝ} (exponentNonnegative : 0 ≤ exponent) :
    Integrable (fun sample => value sample ^ (-exponent)) measure := by
  simpa only [Real.rpow_neg_eq_inv_rpow, Pi.inv_apply] using
    integrable_rpow_of_nat_moments measure measurable.inv
      (fun sample => (inv_pos.mpr (positive sample)).le) naturalInverseMoments exponentNonnegative

end
end IGSIII.Chemical.SmallBall
