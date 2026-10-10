import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import IGSIII.Mass.BorelCantelli

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

theorem ae_tendsto_of_shifted_conditional_comparisons
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (information : ℕ → MeasurableSpace Sample) (sequence : ℕ → Sample → ℝ) (endpoint : Sample → ℝ)
    (shift : ℕ → ℕ) (forwardCoefficient reverseCoefficient : ℕ → ℝ)
    (forwardTendstoZero : Tendsto forwardCoefficient atTop (𝓝 0))
    (reverseTendstoZero : Tendsto reverseCoefficient atTop (𝓝 0))
    (forwardEnvelope reverseEnvelope : Sample → ℝ)
    (forwardConditional : ∀ block, ∀ᵐ sample ∂measure, ∀ᶠ depth : ℕ in atTop,
      measure[fun sample => max (sequence (depth+shift block) sample-endpoint sample) 0 | information depth] sample ≤
        forwardCoefficient block*forwardEnvelope sample)
    (reverseConditional : ∀ block, ∀ᵐ sample ∂measure, ∀ᶠ depth : ℕ in atTop,
      measure[fun sample => max (endpoint sample-sequence (depth+shift block) sample) 0 | information depth] sample ≤
        reverseCoefficient block*reverseEnvelope sample)
    (forwardCentered : ∀ block, ∀ᵐ sample ∂measure,
      Tendsto (fun depth => max (sequence (depth+shift block) sample-endpoint sample) 0-
        measure[fun sample => max (sequence (depth+shift block) sample-endpoint sample) 0 | information depth] sample) atTop (𝓝 0))
    (reverseCentered : ∀ block, ∀ᵐ sample ∂measure,
      Tendsto (fun depth => max (endpoint sample-sequence (depth+shift block) sample) 0-
        measure[fun sample => max (endpoint sample-sequence (depth+shift block) sample) 0 | information depth] sample) atTop (𝓝 0)) :
    ∀ᵐ sample ∂measure, Tendsto (fun depth => sequence depth sample) atTop (𝓝 (endpoint sample)) := by
  filter_upwards [ae_all_iff.mpr forwardConditional, ae_all_iff.mpr reverseConditional,
    ae_all_iff.mpr forwardCentered, ae_all_iff.mpr reverseCentered]
    with sample forwardBounds reverseBounds forwardLimits reverseLimits
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  have coefficients := (forwardTendstoZero.mul_const (forwardEnvelope sample)).add
    (reverseTendstoZero.mul_const (reverseEnvelope sample))
  simp only [zero_mul, zero_add] at coefficients
  obtain ⟨block, smallCoefficient⟩ := (coefficients.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < tolerance/2))).exists
  have centered := (forwardLimits block).add (reverseLimits block)
  simp only [zero_add] at centered
  have shifted : ∀ᶠ depth : ℕ in atTop,
      dist (sequence (depth+shift block) sample) (endpoint sample) < tolerance := by
    filter_upwards [forwardBounds block, reverseBounds block,
      centered.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < tolerance/2))]
      with depth forwardBound reverseBound centeredSmall
    rw [Real.dist_eq]
    have absolute : |sequence (depth+shift block) sample-endpoint sample| =
        max (sequence (depth+shift block) sample-endpoint sample) 0+
          max (endpoint sample-sequence (depth+shift block) sample) 0 := by
      rcases le_total (sequence (depth+shift block) sample) (endpoint sample) with comparison | comparison
      · rw [abs_of_nonpos (sub_nonpos.mpr comparison), max_eq_right (sub_nonpos.mpr comparison),
          max_eq_left (sub_nonneg.mpr comparison)]
        ring
      · rw [abs_of_nonneg (sub_nonneg.mpr comparison), max_eq_left (sub_nonneg.mpr comparison),
          max_eq_right (sub_nonpos.mpr comparison)]
        ring
    rw [absolute]
    linarith
  have mapped : ∀ᶠ depth : ℕ in Filter.map (fun depth : ℕ => depth+shift block) atTop,
      dist (sequence depth sample) (endpoint sample) < tolerance := shifted
  rw [Filter.map_add_atTop_eq_nat] at mapped
  exact eventually_atTop.mp mapped

end
end IGSIII34.Probability

