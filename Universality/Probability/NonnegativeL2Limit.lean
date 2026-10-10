import Universality.Probability.L2LimitOperations
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem nonnegative_L2_limit (f : ℕ → Ω → ℝ) (limit : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hlimit : AEStronglyMeasurable limit μ)
    (hnonneg : ∀ n x, 0 ≤ f n x)
    (hconv : Tendsto (fun n => eLpNorm (f n - limit) 2 μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, 0 ≤ limit x := by
  have hinmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hf hlimit hconv
  obtain ⟨indices, _, hsubsequence⟩ := hinmeasure.exists_seq_tendsto_ae
  filter_upwards [hsubsequence] with x hx
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hx
    (Eventually.of_forall (fun n => hnonneg (indices n) x))

end
end Universality
