import IGSIII34.Diffusion.FlooredIntervalModulusCompletion20261011
import IGSIII34.Diffusion.WeightedCumulativeClockCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal BigOperators

theorem finiteFloor_physical_modulus_of_chain_completion20261011
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    (Vertices : ℕ → Type*) [∀ depth, MeasurableSpace (Vertices depth)]
    (laws : ∀ depth, Measure (ℕ → Vertices depth)) [∀ depth, IsFiniteMeasure (laws depth)]
    (placements : ∀ depth, Vertices depth → Space) (measurable : ∀ depth, Measurable (placements depth))
    (clocks : ℕ → ℝ) (nonnegative : ∀ depth, 0 ≤ clocks depth)
    (chainModulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (laws depth).real (finiteIntervalChainBadModulusCompletion20261011 (placements depth) (clocks depth) horizon duration tolerance) ≤ error)
    (horizon : ℝ≥0) (tolerance error : ℝ) (tolerancePositive : 0 < tolerance) (errorPositive : 0 < error) :
    ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
      ∃ bad : Set (ℕ → Vertices depth), MeasurableSet bad ∧ (laws depth).real bad ≤ error ∧
        ∀ path ∉ bad, ∀ first second : ℝ≥0, first ≤ horizon → second ≤ horizon → dist first second < duration →
          dist (placements depth (path ⌊clocks depth * first⌋₊)) (placements depth (path ⌊clocks depth * second⌋₊)) ≤ tolerance := by
  obtain ⟨duration, positive, probabilities⟩ := chainModulus (⌈(horizon : ℝ)⌉₊) tolerance error tolerancePositive errorPositive
  refine ⟨duration, positive, ?_⟩
  filter_upwards [probabilities] with depth probability
  let bad := finiteIntervalChainBadModulusCompletion20261011 (placements depth) (clocks depth) (⌈(horizon : ℝ)⌉₊) duration tolerance
  refine ⟨bad, finiteIntervalChainBadModulus_measurable_completion20261011 _ (measurable depth) _ _ _ _, probability, ?_⟩
  intro path outside first second firstBound secondBound near
  have firstBefore : (first : ℝ) ≤ (⌈(horizon : ℝ)⌉₊ : ℝ) := (NNReal.coe_le_coe.mpr firstBound).trans (Nat.le_ceil _)
  have secondBefore : (second : ℝ) ≤ (⌈(horizon : ℝ)⌉₊ : ℝ) := (NNReal.coe_le_coe.mpr secondBound).trans (Nat.le_ceil _)
  have indicesNear := natFloor_difference_le_completion20261011 (clocks depth * first) (clocks depth * second)
    (mul_nonneg (nonnegative depth) first.property) (mul_nonneg (nonnegative depth) second.property)
  have difference : |clocks depth * first - clocks depth * second| = clocks depth * dist first second := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (nonnegative depth)]
    rfl
  rw [difference] at indicesNear
  have window := indicesNear.trans (add_le_add (mul_le_mul_of_nonneg_left near.le (nonnegative depth)) le_rfl)
  by_contra failure
  exact outside ⟨_, Nat.floor_mono (mul_le_mul_of_nonneg_left firstBefore (nonnegative depth)),
    _, Nat.floor_mono (mul_le_mul_of_nonneg_left secondBefore (nonnegative depth)), window, lt_of_not_ge failure⟩

theorem chain_modulus_clock_change_completion20261011
    {Space : Type*} [MetricSpace Space]
    (Vertices : ℕ → Type*) [∀ depth, MeasurableSpace (Vertices depth)]
    (laws : ∀ depth, Measure (ℕ → Vertices depth)) [∀ depth, IsFiniteMeasure (laws depth)]
    (placements : ∀ depth, Vertices depth → Space)
    (oldClocks newClocks : ℕ → ℝ) (oldNonnegative : ∀ depth, 0 ≤ oldClocks depth)
    (bound : ℕ) (positive : 0 < bound) (bounded : ∀ᶠ depth in atTop, newClocks depth ≤ bound * oldClocks depth)
    (modulus : ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (laws depth).real (finiteIntervalChainBadModulusCompletion20261011 (placements depth) (oldClocks depth) horizon duration tolerance) ≤ error) :
    ∀ horizon : ℕ, ∀ tolerance error : ℝ, 0 < tolerance → 0 < error →
      ∃ duration : ℝ, 0 < duration ∧ ∀ᶠ depth in atTop,
        (laws depth).real (finiteIntervalChainBadModulusCompletion20261011 (placements depth) (newClocks depth) horizon duration tolerance) ≤ error := by
  intro horizon tolerance error tolerancePositive errorPositive
  obtain ⟨duration, durationPositive, probabilities⟩ := modulus (bound*horizon) tolerance error tolerancePositive errorPositive
  refine ⟨duration/(bound:ℝ), div_pos durationPositive (by exact_mod_cast positive), ?_⟩
  filter_upwards [bounded, probabilities] with depth clockBound probability
  apply (measureReal_mono (μ := laws depth) ?_).trans probability
  intro path failure
  obtain ⟨first, firstBound, second, secondBound, window, distant⟩ := failure
  have horizonBound : newClocks depth * horizon ≤ oldClocks depth * (bound*horizon : ℕ) := by
    have multiplied := mul_le_mul_of_nonneg_right clockBound (by positivity : (0:ℝ) ≤ horizon)
    push_cast
    nlinarith
  have durationBound : newClocks depth * (duration/(bound:ℝ)) ≤ oldClocks depth * duration := by
    have multiplied := mul_le_mul_of_nonneg_right clockBound
      (div_pos durationPositive (by exact_mod_cast positive : (0:ℝ) < (bound:ℝ))).le
    have factor : (bound:ℝ)*oldClocks depth*(duration/(bound:ℝ)) = oldClocks depth*duration := by
      field_simp [show (bound:ℝ) ≠ 0 by exact_mod_cast positive.ne']
    exact factor ▸ multiplied
  exact ⟨first, firstBound.trans (Nat.floor_mono horizonBound), second, secondBound.trans (Nat.floor_mono horizonBound),
    window.trans (by linarith), distant⟩

theorem centered_clock_change_probability_completion20261011
    (Vertices : ℕ → Type*) [∀ depth, MeasurableSpace (Vertices depth)]
    (laws : ∀ depth, Measure (ℕ → Vertices depth))
    (weights : ∀ depth, Vertices depth → ℝ) (oldClocks newClocks : ℕ → ℝ)
    (upper lower : ℝ) (upperPositive : 0 < upper) (lowerPositive : 0 < lower)
    (bounded : ∀ᶠ depth in atTop, lower * oldClocks depth ≤ newClocks depth ∧ newClocks depth ≤ upper * oldClocks depth)
    (oldClock : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => laws depth {path | ∃ count ≤ ⌊oldClocks depth*horizon⌋₊,
        oldClocks depth*tolerance < |centeredWeightClockCompletion20261011 (fun index => weights depth (path index)) count|}) atTop (𝓝 0)) :
    ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => laws depth {path | ∃ count ≤ ⌊newClocks depth*horizon⌋₊,
        newClocks depth*tolerance < |centeredWeightClockCompletion20261011 (fun index => weights depth (path index)) count|}) atTop (𝓝 0) := by
  intro horizon tolerance horizonNonnegative tolerancePositive
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (oldClock (upper*horizon) (lower*tolerance) (mul_nonneg upperPositive.le horizonNonnegative) (mul_pos lowerPositive tolerancePositive))
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [bounded] with depth bounds
  apply measure_mono
  intro path failure
  obtain ⟨count, countBound, large⟩ := failure
  refine ⟨count, countBound.trans (Nat.floor_mono ?_), ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right bounds.2 horizonNonnegative]
  · have comparison := mul_le_mul_of_nonneg_right bounds.1 tolerancePositive.le
    nlinarith

end
end IGSIII34.Diffusion
