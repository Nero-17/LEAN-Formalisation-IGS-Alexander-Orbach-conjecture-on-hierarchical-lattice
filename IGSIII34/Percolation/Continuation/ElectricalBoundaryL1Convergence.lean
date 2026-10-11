import IGSIII34.Percolation.Continuation.ElectricalBoundaryLimitLaw
import IGSIII34.Probability.UniformSecondMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

theorem electrical_same_law_uniformIntegrable_one
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (sequence : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (sequence depth))
    (law : Measure ℝ) [IsProbabilityMeasure law] (lawMemLp : MemLp (fun value : ℝ => value) 2 law)
    (sequenceLaw : ∀ depth, measure.map (sequence depth) = law) : UniformIntegrable sequence 1 measure := by
  have preserving (depth : ℕ) : MeasurePreserving (sequence depth) measure law :=
    ⟨measurable depth, sequenceLaw depth⟩
  have membership (depth : ℕ) : MemLp (sequence depth) 2 measure := by
    simpa only [Function.comp_def] using lawMemLp.comp_measurePreserving (preserving depth)
  have integrable (depth : ℕ) := (membership depth).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have normEquality (depth : ℕ) : eLpNorm (sequence depth) 2 measure = eLpNorm (fun value : ℝ => value) 2 law := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving lawMemLp.aestronglyMeasurable (preserving depth)
  have normOneBound (depth : ℕ) : eLpNorm (sequence depth) 1 measure ≤
      (eLpNorm (fun value : ℝ => value) 2 law).toNNReal := by
    rw [ENNReal.coe_toNNReal lawMemLp.eLpNorm_ne_top]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (measurable depth).aestronglyMeasurable).trans_eq (normEquality depth)
  refine ⟨fun depth => (measurable depth).aestronglyMeasurable, ?_,
    (eLpNorm (fun value : ℝ => value) 2 law).toNNReal, normOneBound⟩
  apply unifIntegrable_one_of_uniform_second_moment measure sequence measurable
    (fun depth => (membership depth).integrable_sq) integrable (∫ value : ℝ, value^2 ∂law)
  intro depth
  have transport := integral_map_of_stronglyMeasurable (μ := measure) (measurable depth)
    (measurable_id.pow_const 2).stronglyMeasurable
  rw [sequenceLaw depth] at transport
  exact transport.symm.le

theorem electrical_constant_law_tendsto_eLpNorm_one
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (sequence : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (sequence depth))
    (law : Measure ℝ) [IsProbabilityMeasure law] (lawMemLp : MemLp (fun value : ℝ => value) 2 law)
    (sequenceLaw : ∀ depth, measure.map (sequence depth) = law)
    (value : Sample → ℝ) (valueMemLp : MemLp value 2 measure)
    (convergence : TendstoInMeasure measure sequence atTop value) :
    Tendsto (fun depth => eLpNorm (fun sample => sequence depth sample-value sample) 1 measure) atTop (𝓝 0) := by
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun depth => (measurable depth).aestronglyMeasurable)
    (valueMemLp.mono_exponent (by norm_num))
    (electrical_same_law_uniformIntegrable_one measure sequence measurable law lawMemLp sequenceLaw).2.1 convergence

end
end IGSIII34.Percolation
