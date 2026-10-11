import IGSIII34.Diffusion.ClockWindowTransferCompletion20261011
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology

def clockFiniteGridTimeCompletion20261011 (grid index : ℕ) : ℝ :=
  index / (grid + 1 : ℝ)

def clockFiniteGridBadCompletion20261011 (acceleration : ℝ) (horizon grid : ℕ)
    (tolerance : ℝ) : Set (ℕ → ℝ) :=
  {holdingTimes | ∃ index : Fin ((horizon + 1) * (grid + 1) + 1),
    tolerance ≤ |(holdingJumpIndex holdingTimes
      (acceleration * clockFiniteGridTimeCompletion20261011 grid index.val) : ℝ) /
        acceleration - clockFiniteGridTimeCompletion20261011 grid index.val|}

theorem clockFiniteGridBad_measurable_completion20261011
    (acceleration : ℝ) (horizon grid : ℕ) (tolerance : ℝ) :
    MeasurableSet (clockFiniteGridBadCompletion20261011 acceleration horizon grid tolerance) := by
  unfold clockFiniteGridBadCompletion20261011
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro index
  have jumpMeasurable : Measurable (fun holdingTimes =>
      (holdingJumpIndex holdingTimes (acceleration * clockFiniteGridTimeCompletion20261011 grid index.val) : ℝ)) :=
    (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp (holdingJumpIndex_measurable _)
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp ((jumpMeasurable.div_const acceleration).sub
      (measurable_const (a := clockFiniteGridTimeCompletion20261011 grid index.val))))

theorem clockFiniteGridTime_bounds_completion20261011 (horizon grid : ℕ)
    (index : Fin ((horizon + 1) * (grid + 1) + 1)) :
    0 ≤ clockFiniteGridTimeCompletion20261011 grid index.val ∧
      clockFiniteGridTimeCompletion20261011 grid index.val ≤ (horizon + 1 : ℕ) := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < grid + 1)).mpr
    have bound : index.val ≤ (horizon + 1) * (grid + 1) := Nat.le_of_lt_succ index.isLt
    exact_mod_cast bound

/-- This clock error event is finite and genuinely Borel measurable.
Its probability tends to zero for the true exponential clock, using the
single universal almost-sure inverse-clock limit already proved. -/
theorem exponential_clock_finite_grid_bad_probability_completion20261011
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop) (horizon grid : ℕ)
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    Tendsto (fun depth => exponentialHoldingTimeLaw.real
      (clockFiniteGridBadCompletion20261011 (acceleration depth) horizon grid tolerance))
      atTop (𝓝 0) := by
  let bad := fun depth => clockFiniteGridBadCompletion20261011 (acceleration depth) horizon grid tolerance
  have badMeasurable (depth : ℕ) : MeasurableSet (bad depth) :=
    clockFiniteGridBad_measurable_completion20261011 _ _ _ _
  have eventuallyGood : ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      ∀ᶠ depth in atTop, holdingTimes ∉ bad depth := by
    filter_upwards [exponentialHoldingTimeLaw_jump_clock_uniform] with holdingTimes uniform
    filter_upwards [uniform acceleration accelerationPositive diverge (horizon + 1 : ℕ)
      (Nat.cast_nonneg _) tolerance tolerancePositive] with depth errors
    rintro ⟨index, badError⟩
    have bounds := clockFiniteGridTime_bounds_completion20261011 horizon grid index
    exact not_le_of_gt (errors _ bounds.1 bounds.2) badError
  have sampleConverges : ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      Tendsto (fun depth => (bad depth).indicator (fun _ : ℕ → ℝ => (1 : ℝ)) holdingTimes) atTop (𝓝 0) := by
    filter_upwards [eventuallyGood] with holdingTimes good
    apply tendsto_const_nhds.congr'
    filter_upwards [good] with depth outside
    exact (Set.indicator_of_notMem outside (fun _ : ℕ → ℝ => (1 : ℝ))).symm
  have dominated := tendsto_integral_of_dominated_convergence (μ := exponentialHoldingTimeLaw)
    (F := fun depth => (bad depth).indicator (fun _ : ℕ → ℝ => (1 : ℝ))) (f := fun _ => (0 : ℝ))
    (fun _ : ℕ → ℝ => (1 : ℝ))
    (fun depth => (measurable_const.indicator (badMeasurable depth)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun depth => Eventually.of_forall (fun holdingTimes => by
      by_cases belongs : holdingTimes ∈ bad depth
      · rw [Set.indicator_of_mem belongs]
        norm_num
      · rw [Set.indicator_of_notMem belongs]
        norm_num))
    sampleConverges
  simpa only [integral_indicator_const (1 : ℝ) (badMeasurable _),
    smul_eq_mul, mul_one, integral_zero, bad] using dominated

end
end IGSIII34.Diffusion
