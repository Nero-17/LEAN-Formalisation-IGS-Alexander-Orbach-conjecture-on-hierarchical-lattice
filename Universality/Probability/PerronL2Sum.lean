import Universality.Probability.L2LimitOperations

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem perron_L2_sum_remainder_zero (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (bound radius : ℝ) (hbound : 0 ≤ bound) (hradius : 1 < radius)
    (hnoise : ∀ n, ∫ x, (f (n + 1) x - radius * f n x) ^ 2 ∂μ ≤ bound * radius ^ n) :
    Tendsto (fun n => eLpNorm (fun x =>
      ((∑ k ∈ Finset.range n, f k x) - f n x / (radius - 1)) / radius ^ n) 2 μ) atTop (𝓝 0) := by
  have hnoiseMem (n : ℕ) : MemLp (fun x => f (n + 1) x - radius * f n x) 2 μ :=
    (hf (n + 1)).sub ((hf n).const_smul radius)
  have hnoiseSum := geometric_second_moment_sum_tendsto_zero (μ := μ)
    (fun n x => f (n + 1) x - radius * f n x) hnoiseMem bound radius hbound hradius hnoise
  have hzero := L2_zero_add (μ := μ)
    (fun n x => f 0 x / radius ^ n)
    (fun n x => (∑ k ∈ Finset.range n, (f (k + 1) x - radius * f k x)) / radius ^ n)
    (fun n => (memLp_div_const_real (hf 0) _).aestronglyMeasurable)
    (fun n => (memLp_div_const_real (memLp_finsetSum (Finset.range n) (fun k _ => hnoiseMem k)) _).aestronglyMeasurable)
    (L2_fixed_div_pow_zero (f 0) (hf 0) radius hradius) hnoiseSum
  have hscaled := L2_zero_smul (μ := μ)
    (fun n => (fun x => f 0 x / radius ^ n) +
      (fun x => (∑ k ∈ Finset.range n, (f (k + 1) x - radius * f k x)) / radius ^ n))
    (-(radius - 1)⁻¹) hzero
  have heq (n : ℕ) : (-(radius - 1)⁻¹) •
      ((fun x => f 0 x / radius ^ n) +
        (fun x => (∑ k ∈ Finset.range n, (f (k + 1) x - radius * f k x)) / radius ^ n)) =
      (fun x => ((∑ k ∈ Finset.range n, f k x) - f n x / (radius - 1)) / radius ^ n) := by
    funext x
    have htelescoping : (∑ k ∈ Finset.range n, (f (k + 1) x - radius * f k x)) =
        f n x - f 0 x - (radius - 1) * ∑ k ∈ Finset.range n, f k x := by
      have hexpand (k : ℕ) : f (k + 1) x - radius * f k x =
          (f (k + 1) x - f k x) - (radius - 1) * f k x := by ring
      simp_rw [hexpand]
      rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => f k x) n, ← Finset.mul_sum]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, htelescoping]
    field_simp [(sub_pos.mpr hradius).ne', (lt_trans zero_lt_one hradius).ne'] <;> ring
  exact hscaled.congr' (Eventually.of_forall (fun n => congrArg (fun g : Ω → ℝ => eLpNorm g 2 μ) (heq n)))

end
end Universality
