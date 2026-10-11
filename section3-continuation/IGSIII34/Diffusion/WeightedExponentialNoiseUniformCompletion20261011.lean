import IGSIII34.Diffusion.WeightedExponentialProductNoiseCompletion20261011
import IGSIII34.Diffusion.WeightedClockGridCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators _root_.Topology
theorem weightedExponentialNoise_product_small_eventually_completion20261011
    (Outcomes : ℕ → Type*) [∀ depth, MeasurableSpace (Outcomes depth)]
    (laws : ∀ depth, Measure (Outcomes depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (weights : ∀ depth, Outcomes depth → ℕ → ℝ)
    (weightsMeasurable : ∀ depth index, Measurable (fun outcome => weights depth outcome index))
    (counts : ℕ → ℕ) (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (bound horizon : ℝ) (boundNonnegative : 0 ≤ bound) (horizonNonnegative : 0 ≤ horizon)
    (bounded : ∀ depth outcome index, index < counts depth → |weights depth outcome index| ≤ bound)
    (countBound : ∀ᶠ depth in atTop, (counts depth : ℝ) ≤ acceleration depth * horizon + 1)
    (divergence : Tendsto acceleration atTop atTop) (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    Tendsto (fun depth => (laws depth).prod exponentialHoldingTimeLaw {sample | acceleration depth * tolerance ≤
      |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) (counts depth) sample.2|})
      atTop (𝓝 0) := by
  have inverse : Tendsto (fun depth => (acceleration depth)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp divergence
  have comparison : Tendsto (fun depth => ENNReal.ofReal
      ((horizon / acceleration depth + 1 / acceleration depth ^ 2) * (bound ^ 2 / tolerance ^ 2))) atTop (𝓝 0) := by
    have first := inverse.const_mul horizon
    have second := inverse.pow 2
    have combined := (first.add second).mul_const (bound ^ 2 / tolerance ^ 2)
    have realConvergence : Tendsto (fun depth =>
      (horizon / acceleration depth + 1 / acceleration depth ^ 2) * (bound ^ 2 / tolerance ^ 2)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_zero, zero_add, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using combined
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp realConvergence
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds comparison (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [countBound] with depth countBound
  have estimate := weightedExponentialNoise_product_probability_bound_completion20261011 (laws depth)
    (weights depth) (weightsMeasurable depth) (counts depth) bound (acceleration depth * tolerance)
    (mul_pos (accelerationPositive depth) tolerancePositive) (bounded depth)
  apply estimate.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((acceleration depth * horizon + 1) * bound ^ 2) / (acceleration depth * tolerance) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right countBound (sq_nonneg bound)) (sq_nonneg _)
    _ = _ := by field_simp [(accelerationPositive depth).ne', tolerancePositive.ne'] <;> ring


theorem weightedExponentialNoise_uniform_probability_completion20261011
    (Outcomes : ℕ → Type*) [∀ depth, MeasurableSpace (Outcomes depth)]
    (laws : ∀ depth, Measure (Outcomes depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (weights : ∀ depth, Outcomes depth → ℕ → ℝ)
    (weightsMeasurable : ∀ depth index, Measurable (fun outcome => weights depth outcome index))
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (weightsNonnegative : ∀ depth outcome index, 0 ≤ weights depth outcome index)
    (weightsBounded : ∀ depth outcome index, weights depth outcome index ≤ bound)
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (divergence : Tendsto acceleration atTop atTop)
    (horizon tolerance : ℝ) (horizonNonnegative : 0 ≤ horizon) (tolerancePositive : 0 < tolerance) :
    Tendsto (fun depth => (laws depth).prod exponentialHoldingTimeLaw
      {sample | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧
        acceleration depth * tolerance <
          |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) count sample.2|}) atTop (𝓝 0) := by
  let duration := tolerance / (4 * (bound + 1))
  let gridTolerance := tolerance / 4
  have durationPositive : 0 < duration := div_pos tolerancePositive (by positivity)
  have gridTolerancePositive : 0 < gridTolerance := by dsimp [gridTolerance]; positivity
  have durationBound : bound * duration ≤ tolerance / 4 := by
    have identity : (4 * (bound + 1)) * duration = tolerance := by
      dsimp only [duration]
      field_simp
    nlinarith [mul_nonneg boundNonnegative durationPositive.le]
  obtain ⟨blocks, blocksLarge⟩ := exists_nat_ge (horizon / duration)
  have horizonBound : horizon ≤ (blocks : ℝ) * duration :=
    (div_le_iff₀ durationPositive).mp blocksLarge
  let stride := fun depth => ⌈acceleration depth * duration⌉₊
  have stridePositive (depth : ℕ) : 0 < stride depth :=
    Nat.ceil_pos.mpr (mul_pos (accelerationPositive depth) durationPositive)
  let gridBad := fun depth => {sample : Outcomes depth × (ℕ → ℝ) |
    ∃ index : Fin (blocks + 1), acceleration depth * gridTolerance ≤
      |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) (index.val * stride depth) sample.2|}
  have gridConvergence : Tendsto (fun depth => (laws depth).prod exponentialHoldingTimeLaw (gridBad depth)) atTop (𝓝 0) := by
    have points : ∀ index : Fin (blocks + 1), Tendsto (fun depth => (laws depth).prod exponentialHoldingTimeLaw
        {sample | acceleration depth * gridTolerance ≤
          |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) (index.val * stride depth) sample.2|})
        atTop (𝓝 0) := by
      intro index
      apply weightedExponentialNoise_product_small_eventually_completion20261011 Outcomes laws weights weightsMeasurable
        (fun depth => index.val * stride depth) acceleration accelerationPositive bound
        ((index.val : ℝ) * (duration + 1)) boundNonnegative (by positivity)
        (fun depth outcome step _ => by rw [abs_of_nonneg (weightsNonnegative depth outcome step)]; exact weightsBounded depth outcome step)
        _ divergence gridTolerance gridTolerancePositive
      filter_upwards [divergence.eventually (eventually_ge_atTop (1 : ℝ))] with depth large
      have rounded := (Nat.ceil_lt_add_one (mul_nonneg (accelerationPositive depth).le durationPositive.le)).le
      have multiplied := mul_le_mul_of_nonneg_left rounded (Nat.cast_nonneg index.val : (0 : ℝ) ≤ index.val)
      dsimp only [stride]
      simp only [Nat.cast_mul] at multiplied ⊢
      nlinarith [show (0 : ℝ) ≤ index.val by positivity]
    have finiteSum := tendsto_finsetSum Finset.univ (fun index _ => points index)
    have zeroSum : (∑ _index : Fin (blocks + 1), (0 : ENNReal)) = 0 := by simp
    rw [zeroSum] at finiteSum
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds finiteSum (fun _ => bot_le)
    intro depth
    simpa only [gridBad, Set.setOf_exists] using
      measure_iUnion_fintype_le (μ := (laws depth).prod exponentialHoldingTimeLaw)
        (fun index : Fin (blocks + 1) => {sample | acceleration depth * gridTolerance ≤
          |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) (index.val * stride depth) sample.2|})
  let clockBad := toMeasurable exponentialHoldingTimeLaw {holding : ℕ → ℝ | ¬ ∀ index, 0 < holding index}
  have clockBadNull : exponentialHoldingTimeLaw clockBad = 0 := by
    rw [measure_toMeasurable]
    exact (ae_iff.mp exponentialHoldingTimeLaw_positive)
  have inverse := (tendsto_inv_atTop_zero.comp divergence).const_mul bound
  have smallInverse : ∀ᶠ depth in atTop, bound / acceleration depth < tolerance / 4 := by
    have convergence : Tendsto (fun depth => bound / acceleration depth) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using inverse
    exact convergence.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds gridConvergence
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [smallInverse] with depth small
  let bad := {sample : Outcomes depth × (ℕ → ℝ) | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧
    acceleration depth * tolerance < |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) count sample.2|}
  have containment : bad ⊆ gridBad depth ∪ Set.univ ×ˢ clockBad := by
    intro sample badSample
    by_cases gridFailure : sample ∈ gridBad depth
    · exact Or.inl gridFailure
    by_cases clockFailure : sample.2 ∈ clockBad
    · exact Or.inr ⟨Set.mem_univ _, clockFailure⟩
    have positive : ∀ index, 0 < sample.2 index := by
      by_contra failure
      exact clockFailure (subset_toMeasurable exponentialHoldingTimeLaw _ failure)
    obtain ⟨count, countBound, failure⟩ := badSample
    have countGridBound : count ≤ blocks * stride depth := by
      have countReal : (count : ℝ) ≤ acceleration depth * horizon :=
        (Nat.cast_le.mpr countBound).trans (Nat.floor_le (mul_nonneg (accelerationPositive depth).le horizonNonnegative))
      have rounded := Nat.le_ceil (acceleration depth * duration)
      have gridReal : (count : ℝ) ≤ ((blocks * stride depth : ℕ) : ℝ) := by
        simp only [Nat.cast_mul]
        nlinarith [mul_le_mul_of_nonneg_left horizonBound (accelerationPositive depth).le,
          mul_le_mul_of_nonneg_left rounded (Nat.cast_nonneg blocks : (0 : ℝ) ≤ blocks)]
      exact_mod_cast gridReal
    have gridGood (index : ℕ) (indexBound : index ≤ blocks) :
        |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) (index * stride depth) sample.2| ≤
          acceleration depth * gridTolerance := by
      apply le_of_lt
      apply lt_of_not_ge
      intro failed
      exact gridFailure ⟨⟨index, Nat.lt_succ_of_le indexBound⟩, failed⟩
    have uniform := weightedExponentialNoise_uniform_of_index_grid_completion20261011 (weights depth sample.1) sample.2
      bound (acceleration depth * gridTolerance) boundNonnegative
      (weightsNonnegative depth sample.1) (weightsBounded depth sample.1) (fun index => (positive index).le)
      (stride depth) blocks (stridePositive depth) gridGood count countGridBound
    have rounded := (Nat.ceil_lt_add_one (mul_nonneg (accelerationPositive depth).le durationPositive.le)).le
    have remainder : bound < acceleration depth * (tolerance / 4) := by
      simpa only [mul_comm] using (div_lt_iff₀ (accelerationPositive depth)).mp small
    have strideBound : bound * stride depth ≤ acceleration depth * (tolerance / 2) := by
      have multiplied := mul_le_mul_of_nonneg_left rounded boundNonnegative
      have durationScaled := mul_le_mul_of_nonneg_left durationBound (accelerationPositive depth).le
      dsimp only [stride] at multiplied ⊢
      nlinarith
    dsimp only [gridTolerance] at uniform
    have contradiction : |weightedExponentialNoiseCompletion20261011 (weights depth sample.1) count sample.2| <
        acceleration depth * tolerance := by
      nlinarith [mul_pos (accelerationPositive depth) tolerancePositive]
    exact False.elim (lt_asymm failure contradiction)
  calc
    _ ≤ (laws depth).prod exponentialHoldingTimeLaw (gridBad depth ∪ Set.univ ×ˢ clockBad) := measure_mono containment
    _ ≤ (laws depth).prod exponentialHoldingTimeLaw (gridBad depth) +
        (laws depth).prod exponentialHoldingTimeLaw (Set.univ ×ˢ clockBad) := measure_union_le _ _
    _ = _ := by rw [Measure.prod_prod, measure_univ, clockBadNull]; simp

end
end IGSIII34.Diffusion
