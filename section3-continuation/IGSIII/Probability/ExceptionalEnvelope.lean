import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Probability

open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem exists_lp_dominator_of_summable_exceptions
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    [IsProbabilityMeasure measure] (order : ℝ≥0∞) [Fact (1 ≤ order)]
    (sequence : ℕ → Sample → ℝ) (bound : Lp ℝ order measure)
    (boundNonnegative : ∀ᵐ sample ∂measure, 0 ≤ bound sample)
    (exceptions : ℕ → Set Sample) (measurable : ∀ depth, MeasurableSet (exceptions depth))
    (weight : ℕ → ℝ) (weightNonnegative : ∀ depth, 0 ≤ weight depth)
    (sequenceBound : ∀ᵐ sample ∂measure, ∀ depth,
      sequence depth sample ≤ bound sample + (exceptions depth).indicator (fun _ => weight depth) sample)
    (summableNorms : ∑' depth, eLpNorm ((exceptions depth).indicator (fun _ => weight depth)) order measure ≠ ∞) :
    ∃ dominator : Lp ℝ order measure,
      (∀ᵐ sample ∂measure, 0 ≤ dominator sample) ∧
      ∀ᵐ sample ∂measure, ∀ depth, sequence depth sample ≤ dominator sample := by
  let exceptional : ℕ → Lp ℝ order measure := fun depth =>
    ((memLp_const (μ := measure) (p := order) (weight depth)).indicator (measurable depth)).toLp
      ((exceptions depth).indicator (fun _ => weight depth))
  have representatives : ∀ᵐ sample ∂measure, ∀ depth,
      exceptional depth sample = (exceptions depth).indicator (fun _ => weight depth) sample :=
    ae_all_iff.mpr (fun _ => MemLp.coeFn_toLp _)
  have finiteNorms : ∑' depth, ‖exceptional depth‖ₑ ≠ ∞ := by
    convert summableNorms using 1
    apply tsum_congr
    intro depth
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp _)
  have sumIdentity := Lp.hasSum_coeFn_tsum finiteNorms
  refine ⟨bound + ∑' depth, exceptional depth, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add bound (∑' depth, exceptional depth), representatives,
      sumIdentity, boundNonnegative] with sample additionEquality sampleRepresentatives sampleSum sampleBound
    rw [additionEquality, Pi.add_apply]
    have nonnegative (depth : ℕ) : 0 ≤ exceptional depth sample := by
      rw [sampleRepresentatives depth]
      exact (indicator_nonneg (s := exceptions depth) (fun _ _ => weightNonnegative depth)) sample
    exact add_nonneg sampleBound (sampleSum.tsum_eq.symm ▸ tsum_nonneg nonnegative)
  · filter_upwards [Lp.coeFn_add bound (∑' depth, exceptional depth), representatives,
      sumIdentity, sequenceBound] with sample additionEquality sampleRepresentatives sampleSum sampleBounds
    intro depth
    rw [additionEquality, Pi.add_apply]
    have nonnegative (index : ℕ) : 0 ≤ exceptional index sample := by
      rw [sampleRepresentatives index]
      exact (indicator_nonneg (s := exceptions index) (fun _ _ => weightNonnegative index)) sample
    have termBound : exceptional depth sample ≤ (∑' index, exceptional index) sample := by
      rw [← sampleSum.tsum_eq]
      simpa only [Finset.sum_singleton] using
        sampleSum.summable.sum_le_tsum {depth} (fun index _ => nonnegative index)
    exact (sampleBounds depth).trans (add_le_add le_rfl (by rwa [sampleRepresentatives depth] at termBound))

theorem supremum_memLp_of_lp_dominator
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) (order : ℝ≥0∞)
    (sequence : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (sequence depth))
    (nonnegative : ∀ᵐ sample ∂measure, ∀ depth, 0 ≤ sequence depth sample)
    (dominator : Lp ℝ order measure)
    (bounds : ∀ᵐ sample ∂measure, ∀ depth, sequence depth sample ≤ dominator sample) :
    MemLp (fun sample => ⨆ depth, sequence depth sample) order measure ∧
      ∀ᵐ sample ∂measure, ∀ depth, sequence depth sample ≤ ⨆ index, sequence index sample := by
  have boundedAbove : ∀ᵐ sample ∂measure,
      BddAbove (Set.range (fun depth => sequence depth sample)) := by
    filter_upwards [bounds] with sample sampleBounds
    exact ⟨dominator sample, by rintro _ ⟨depth, rfl⟩; exact sampleBounds depth⟩
  constructor
  · apply (Lp.memLp dominator).mono'
      ((Measurable.iSup measurable).aestronglyMeasurable)
    filter_upwards [bounds, boundedAbove, nonnegative] with sample sampleBounds sampleBounded sampleNonnegative
    rw [Real.norm_eq_abs, abs_of_nonneg ((sampleNonnegative 0).trans (le_ciSup sampleBounded 0))]
    exact ciSup_le sampleBounds
  · filter_upwards [boundedAbove] with sample sampleBounded
    exact fun depth => le_ciSup sampleBounded depth

end IGSIII.Probability
