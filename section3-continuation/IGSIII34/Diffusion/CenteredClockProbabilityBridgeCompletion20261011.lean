import IGSIII34.Diffusion.WeightedCumulativeClockCompletion20261011
import IGSIII34.Diffusion.ResolventAdditiveClockCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators _root_.Topology

theorem centeredClock_probability_of_scaled_real_completion20261011
    (Vertices : ℕ → Type*) [∀ depth, MeasurableSpace (Vertices depth)]
    (laws : ∀ depth, Measure (ℕ → Vertices depth)) [∀ depth, IsProbabilityMeasure (laws depth)]
    (weights : ∀ depth, Vertices depth → ℝ)
    (acceleration : ℕ → ℝ) (positive : ∀ depth, 0 < acceleration depth)
    (scaled : ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => (laws depth).real
        {path | ∃ count ≤ ⌊acceleration depth * horizon⌋₊,
          tolerance ≤ |finiteWalkScaledAdditiveCompletion20261011 (acceleration depth)
            (fun vertex => weights depth vertex - 1) count path|}) atTop (𝓝 0)) :
    ∀ horizon tolerance : ℝ, 0 ≤ horizon → 0 < tolerance →
      Tendsto (fun depth => laws depth
        {path | ∃ count, count ≤ ⌊acceleration depth * horizon⌋₊ ∧ acceleration depth * tolerance <
          |centeredWeightClockCompletion20261011 (fun index => weights depth (path index)) count|}) atTop (𝓝 0) := by
  intro horizon tolerance nonnegative tolerancePositive
  have upper := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (scaled horizon tolerance nonnegative tolerancePositive)
  simp only [ENNReal.ofReal_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper (fun _ => bot_le)
  intro depth
  dsimp only [Function.comp_apply]
  rw [ofReal_measureReal]
  apply measure_mono
  intro path failure
  obtain ⟨count, bounded, failure⟩ := failure
  refine ⟨count, bounded, ?_⟩
  change tolerance ≤ |(∑ index ∈ Finset.range count, (weights depth (path index) - 1)) / acceleration depth|
  rw [abs_div, abs_of_pos (positive depth)]
  exact (le_div_iff₀ (positive depth)).mpr (by
    simpa only [centeredWeightClockCompletion20261011, mul_comm] using failure.le)

end
end IGSIII34.Diffusion
