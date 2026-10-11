import IGSIII34.Diffusion.ActualNaturalClockDivergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

/-- Divergence already gives eventual positivity; no condition on a finite
initial segment of the acceleration sequence is needed. -/
theorem holdingClock_floor_uniform_of_divergence (holdingTimes : ℕ → ℝ)
    (average : Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ))
      atTop (𝓝 1)) (acceleration : ℕ → ℝ) (accelerationDiverges : Tendsto acceleration atTop atTop)
    (horizon : ℝ) (horizonNonnegative : 0 ≤ horizon) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ time : ℝ,
      0 ≤ time → time ≤ horizon →
      |dePoissonizationClock holdingTimes (acceleration depth) time - time| < tolerance := by
  have adjustedDiverges : Tendsto (fun depth => max 1 (acceleration depth)) atTop atTop :=
    tendsto_atTop_mono (fun depth => le_max_right _ _) accelerationDiverges
  intro tolerance tolerancePositive
  have adjustedClock := holdingClock_floor_uniform holdingTimes average
    (fun depth => max 1 (acceleration depth)) (fun depth => zero_lt_one.trans_le (le_max_left _ _))
    adjustedDiverges horizon horizonNonnegative tolerance tolerancePositive
  filter_upwards [adjustedClock, accelerationDiverges.eventually (eventually_ge_atTop 1)] with depth clock large
  simpa only [dePoissonizationClock, max_eq_right large] using clock

theorem holdingJumpClock_uniform_of_divergence (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (average : Tendsto (fun count => cumulativeHoldingTime holdingTimes count / (count : ℝ))
      atTop (𝓝 1)) (acceleration : ℕ → ℝ) (accelerationDiverges : Tendsto acceleration atTop atTop)
    (horizon : ℝ) (horizonNonnegative : 0 ≤ horizon) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ time : ℝ,
      0 ≤ time → time ≤ horizon →
      |(holdingJumpIndex holdingTimes (acceleration depth * time) : ℝ) / acceleration depth - time| < tolerance := by
  have adjustedDiverges : Tendsto (fun depth => max 1 (acceleration depth)) atTop atTop :=
    tendsto_atTop_mono (fun depth => le_max_right _ _) accelerationDiverges
  intro tolerance tolerancePositive
  have adjustedClock := holdingJumpClock_uniform holdingTimes positive nonexplosion average
    (fun depth => max 1 (acceleration depth)) (fun depth => zero_lt_one.trans_le (le_max_left _ _))
    adjustedDiverges horizon horizonNonnegative tolerance tolerancePositive
  filter_upwards [adjustedClock, accelerationDiverges.eventually (eventually_ge_atTop 1)] with depth clock large
  simpa only [max_eq_right large] using clock

/-- Both manuscript natural clocks, on the actual environment and independent
waiting-time laws, satisfy both uniform de-Poissonisation clock limits. -/
theorem actual_natural_dePoissonization_clocks {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (resistance : ℝ)
    (resistanceGrowthLower : deriv rule.network.reliability p ≤ resistance) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
        ∀ acceleration : ℕ → ℝ,
          (acceleration = (fun depth => 2 *
            ((rule.generation depth).network.liveCount .connected .connected
              (markedGenerationConfiguration rule marks depth [] true) : ℝ) * resistance ^ depth) ∨
           acceleration = (fun depth => (markedComponentVertexMass rule marks depth [] + 2) * resistance ^ depth)) →
          ∀ horizon : ℝ, 0 ≤ horizon → ∀ tolerance : ℝ, 0 < tolerance →
            (∀ᶠ depth in atTop, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
              |dePoissonizationClock holdingTimes (acceleration depth) time - time| < tolerance) ∧
            (∀ᶠ depth in atTop, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
              |(holdingJumpIndex holdingTimes (acceleration depth * time) : ℝ) /
                acceleration depth - time| < tolerance) := by
  filter_upwards [actual_natural_clocks_diverge classicalRule p positive belowOne fixedPoint resistance resistanceGrowthLower]
    with marks divergences
  filter_upwards [exponentialHoldingTimeLaw_positive, exponentialHoldingTimeLaw_nonexplosion,
    exponentialHoldingTimeLaw_clock_average] with holdingTimes waitingPositive nonexplosion average
  intro acceleration natural horizon horizonNonnegative tolerance tolerancePositive
  have accelerationDiverges : Tendsto acceleration atTop atTop := by
    rcases natural with natural | natural
    · simpa only [natural] using divergences.1
    · simpa only [natural] using divergences.2
  exact ⟨holdingClock_floor_uniform_of_divergence holdingTimes average acceleration accelerationDiverges
    horizon horizonNonnegative tolerance tolerancePositive,
    holdingJumpClock_uniform_of_divergence holdingTimes waitingPositive nonexplosion average acceleration accelerationDiverges
      horizon horizonNonnegative tolerance tolerancePositive⟩

end
end IGSIII34.Diffusion
