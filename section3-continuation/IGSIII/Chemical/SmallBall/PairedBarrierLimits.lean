import IGSIII.Chemical.SmallBall.PairedUniformBarrier
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

variable {Sample : Type*} [MeasurableSpace Sample]

/-- A uniform event bound passes to an event whose points eventually lie in
the approximating events. Measurability of those events is not needed. -/
theorem measure_le_of_ae_eventually_mem (measure : Measure Sample)
    (event : Set Sample) (approximatingEvent : ℕ → Set Sample) (bound : ℝ≥0∞)
    (eventuallyMem : ∀ᵐ sample ∂measure, sample ∈ event → ∀ᶠ depth in atTop,
      sample ∈ approximatingEvent depth)
    (bounds : ∀ depth, measure (approximatingEvent depth) ≤ bound) : measure event ≤ bound := by
  let tailEvent (start : ℕ) : Set Sample :=
    {sample | ∀ depth, start ≤ depth → sample ∈ approximatingEvent depth}
  have increasing : Monotone tailEvent := by
    intro first second order sample membership depth depthLower
    exact membership depth (order.trans depthLower)
  have eventSubset : event ≤ᵐ[measure] ⋃ start, tailEvent start := by
    filter_upwards [eventuallyMem] with sample implication membership
    obtain ⟨start, valid⟩ := eventually_atTop.mp (implication membership)
    exact mem_iUnion.mpr ⟨start, valid⟩
  calc
    measure event ≤ measure (⋃ start, tailEvent start) := measure_mono_ae eventSubset
    _ = ⨆ start, measure (tailEvent start) := increasing.measure_iUnion
    _ ≤ bound := iSup_le (fun start =>
      (measure_mono (show tailEvent start ⊆ approximatingEvent start from
        fun sample membership => membership start le_rfl)).trans (bounds start))

theorem paired_comparison_bound_of_ae_tendsto (measure : Measure Sample)
    (first second : ℕ → Sample → ℝ) (firstLimit secondLimit : Sample → ℝ)
    (scale : ℝ) (bound : ℝ≥0∞)
    (convergence : ∀ᵐ sample ∂measure,
      Tendsto (fun depth => first depth sample) atTop (𝓝 (firstLimit sample)) ∧
        Tendsto (fun depth => second depth sample) atTop (𝓝 (secondLimit sample)))
    (bounds : ∀ depth, measure {sample | scale * second depth sample < first depth sample} ≤ bound) :
    measure {sample | scale * secondLimit sample < firstLimit sample} ≤ bound := by
  apply measure_le_of_ae_eventually_mem measure _ _ bound _ bounds
  filter_upwards [convergence] with sample limits bad
  exact (limits.2.const_mul scale).eventually_lt limits.1 bad

theorem ae_paired_comparison_of_bounds_tendsto_zero (measure : Measure Sample)
    (first second : Sample → ℝ) (scale : ℝ) (error : ℕ → ℝ)
    (errorTendstoZero : Tendsto error atTop (𝓝 0))
    (bounds : ∀ depth, measure {sample | scale * second sample < first sample} ≤ ENNReal.ofReal (error depth)) :
    ∀ᵐ sample ∂measure, first sample ≤ scale * second sample := by
  have limit : Tendsto (fun depth => ENNReal.ofReal (error depth)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp errorTendstoZero
  have zero : measure {sample | scale * second sample < first sample} = 0 :=
    le_antisymm (ge_of_tendsto' limit bounds) bot_le
  simpa only [ae_iff, not_le] using zero

/-- Simultaneous comparability is asserted only for a countable family. -/
theorem ae_countable_paired_comparison_of_bounds_tendsto_zero
    {Index : Type*} [Countable Index] (measure : Measure Sample)
    (value : Index → Sample → ℝ) (scale : ℝ) (error : ℕ → ℝ)
    (errorTendstoZero : Tendsto error atTop (𝓝 0))
    (bounds : ∀ first second depth,
      measure {sample | scale * value second sample < value first sample} ≤ ENNReal.ofReal (error depth)) :
    ∀ᵐ sample ∂measure, ∀ first second, value first sample ≤ scale * value second sample := by
  rw [ae_all_iff]
  intro first
  rw [ae_all_iff]
  intro second
  exact ae_paired_comparison_of_bounds_tendsto_zero measure (value first) (value second) scale error
    errorTendstoZero (bounds first second)

end
end IGSIII.Chemical.SmallBall
