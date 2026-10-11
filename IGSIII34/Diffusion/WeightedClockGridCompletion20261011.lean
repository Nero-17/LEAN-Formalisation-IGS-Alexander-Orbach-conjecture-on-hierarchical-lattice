import IGSIII34.Diffusion.WeightedExponentialNoiseCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped BigOperators _root_.Topology

/-- Monotonicity controls all jump indices from a fixed finite clock grid.
Only the deterministic mean clock needs a Lipschitz bound. -/
theorem monotoneClock_error_of_index_grid_completion20261011
    (clock mean : ℕ → ℝ) (clockMonotone : Monotone clock)
    (bound tolerance : ℝ) (boundNonnegative : 0 ≤ bound)
    (meanLipschitz : ∀ first last, first ≤ last →
      |mean last - mean first| ≤ bound * ((last : ℝ) - first))
    (stride blocks : ℕ) (stridePositive : 0 < stride)
    (gridGood : ∀ index ≤ blocks, |clock (index * stride) - mean (index * stride)| ≤ tolerance)
    (count : ℕ) (countBound : count ≤ blocks * stride) :
    |clock count - mean count| ≤ tolerance + bound * stride := by
  by_cases terminal : count = blocks * stride
  · subst count
    exact (gridGood blocks le_rfl).trans (le_add_of_nonneg_right (mul_nonneg boundNonnegative (Nat.cast_nonneg _)))
  have before : count < blocks * stride := lt_of_le_of_ne countBound terminal
  let lower := count / stride
  have lowerSmall : lower < blocks := (Nat.div_lt_iff_lt_mul stridePositive).mpr before
  have lowerBefore : lower * stride ≤ count := Nat.div_mul_le_self count stride
  have upperAfter : count < (lower + 1) * stride := by
    have remainder := Nat.mod_lt count stridePositive
    have quotient := Nat.mod_add_div count stride
    dsimp only [lower]
    nlinarith
  have lowerClose : (count : ℝ) - (lower * stride : ℕ) ≤ stride := by
    have upperReal : (count : ℝ) ≤ ((lower + 1) * stride : ℕ) := Nat.cast_le.mpr upperAfter.le
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at upperReal ⊢
    nlinarith
  have upperClose : (((lower + 1) * stride : ℕ) : ℝ) - count ≤ stride := by
    have lowerReal : ((lower * stride : ℕ) : ℝ) ≤ count := Nat.cast_le.mpr lowerBefore
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at lowerReal ⊢
    nlinarith
  have lowerMean := meanLipschitz (lower * stride) count lowerBefore
  have upperMean := meanLipschitz count ((lower + 1) * stride) upperAfter.le
  have lowerMeanBound := lowerMean.trans (mul_le_mul_of_nonneg_left lowerClose boundNonnegative)
  have upperMeanBound := upperMean.trans (mul_le_mul_of_nonneg_left upperClose boundNonnegative)
  have lowerGood := gridGood lower lowerSmall.le
  have upperGood := gridGood (lower + 1) lowerSmall
  have lowerClock := clockMonotone lowerBefore
  have upperClock := clockMonotone upperAfter.le
  rw [abs_le] at lowerMeanBound upperMeanBound lowerGood upperGood ⊢
  constructor <;> linarith

theorem cumulativeMeanClock_lipschitz_completion20261011
    (weights : ℕ → ℝ) (bound : ℝ)
    (nonnegative : ∀ index, 0 ≤ weights index) (bounded : ∀ index, weights index ≤ bound)
    (first last : ℕ) (ordered : first ≤ last) :
    |(∑ index ∈ Finset.range last, weights index) - (∑ index ∈ Finset.range first, weights index)| ≤
      bound * ((last : ℝ) - first) := by
  have estimates : ∀ last, first ≤ last →
      0 ≤ (∑ index ∈ Finset.range last, weights index) - (∑ index ∈ Finset.range first, weights index) ∧
      (∑ index ∈ Finset.range last, weights index) - (∑ index ∈ Finset.range first, weights index) ≤
        bound * ((last : ℝ) - first) := by
    intro last ordered
    induction last, ordered using Nat.le_induction with
    | base => simp
    | succ last ordered induction =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      constructor
      · linarith [nonnegative last]
      · nlinarith [bounded last]
  exact (abs_of_nonneg (estimates last ordered).1).trans_le (estimates last ordered).2

theorem cumulativeWeightedHoldingClock_monotone_completion20261011
    (weights holding : ℕ → ℝ) (weightsNonnegative : ∀ index, 0 ≤ weights index)
    (holdingNonnegative : ∀ index, 0 ≤ holding index) :
    Monotone (fun count => ∑ index ∈ Finset.range count, weights index * holding index) := by
  apply monotone_nat_of_le_succ
  intro count
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (mul_nonneg (weightsNonnegative count) (holdingNonnegative count))

theorem weightedExponentialNoise_uniform_of_index_grid_completion20261011
    (weights holding : ℕ → ℝ) (bound tolerance : ℝ) (boundNonnegative : 0 ≤ bound)
    (weightsNonnegative : ∀ index, 0 ≤ weights index) (weightsBounded : ∀ index, weights index ≤ bound)
    (holdingNonnegative : ∀ index, 0 ≤ holding index)
    (stride blocks : ℕ) (stridePositive : 0 < stride)
    (gridGood : ∀ index ≤ blocks,
      |weightedExponentialNoiseCompletion20261011 weights (index * stride) holding| ≤ tolerance)
    (count : ℕ) (countBound : count ≤ blocks * stride) :
    |weightedExponentialNoiseCompletion20261011 weights count holding| ≤ tolerance + bound * stride := by
  have identity (count : ℕ) : weightedExponentialNoiseCompletion20261011 weights count holding =
      (∑ index ∈ Finset.range count, weights index * holding index) - ∑ index ∈ Finset.range count, weights index := by
    simp only [weightedExponentialNoiseCompletion20261011, mul_sub, mul_one, Finset.sum_sub_distrib]
  simp_rw [identity] at gridGood ⊢
  exact monotoneClock_error_of_index_grid_completion20261011 _ _
    (cumulativeWeightedHoldingClock_monotone_completion20261011 weights holding weightsNonnegative holdingNonnegative)
    bound tolerance boundNonnegative (cumulativeMeanClock_lipschitz_completion20261011 weights bound weightsNonnegative weightsBounded)
    stride blocks stridePositive gridGood count countBound

end
end IGSIII34.Diffusion
