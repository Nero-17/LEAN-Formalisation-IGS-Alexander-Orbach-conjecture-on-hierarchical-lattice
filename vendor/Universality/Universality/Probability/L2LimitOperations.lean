import Universality.Probability.SubcriticalL2Recursion

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_div_const_real {f : Ω → ℝ} (hf : MemLp f 2 μ) (constant : ℝ) :
    MemLp (fun x => f x / constant) 2 μ := by
  simpa only [div_eq_mul_inv] using hf.mul_const constant⁻¹

theorem L2_zero_add (f g : ℕ → Ω → ℝ)
    (hfmeas : ∀ n, AEStronglyMeasurable (f n) μ) (hgmeas : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n + g n) 2 μ) atTop (𝓝 0) := by
  have hsum := hf.add hg
  simp only [zero_add] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun n => eLpNorm_add_le (hfmeas n) (hgmeas n) (by norm_num))

theorem L2_zero_smul (f : ℕ → Ω → ℝ) (constant : ℝ)
    (hf : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (constant • f n) 2 μ) atTop (𝓝 0) := by
  simpa only [eLpNorm_const_smul, mul_zero] using
    ENNReal.Tendsto.const_mul hf (Or.inr (by simp : ‖constant‖ₑ ≠ ∞))

theorem L2_fixed_div_pow_zero (f : Ω → ℝ) (hf : MemLp f 2 μ) (radius : ℝ) (hradius : 1 < radius) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => f x / radius ^ n) 2 μ) atTop (𝓝 0) := by
  apply L2_normalized_geometric_bound_zero (fun _ => f) (eLpNorm f 2 μ).toReal 1 radius
    zero_le_one (lt_trans zero_lt_one hradius) hradius
  intro n
  rw [one_pow, mul_one, ENNReal.ofReal_toReal hf.eLpNorm_lt_top.ne]

theorem L2_limit_add (f g : ℕ → Ω → ℝ) (first second : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hfirst : MemLp first 2 μ) (hsecond : MemLp second 2 μ)
    (hflimit : Tendsto (fun n => eLpNorm (f n - first) 2 μ) atTop (𝓝 0))
    (hglimit : Tendsto (fun n => eLpNorm (g n - second) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((f n + g n) - (first + second)) 2 μ) atTop (𝓝 0) := by
  have heq (n : ℕ) : (f n + g n) - (first + second) = (f n - first) + (g n - second) := by abel
  simp_rw [heq]
  exact L2_zero_add _ _ (fun n => ((hf n).sub hfirst).aestronglyMeasurable)
    (fun n => ((hg n).sub hsecond).aestronglyMeasurable) hflimit hglimit

theorem L2_limit_smul (f : ℕ → Ω → ℝ) (limit : Ω → ℝ) (constant : ℝ)
    (hlimit : Tendsto (fun n => eLpNorm (f n - limit) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (constant • f n - constant • limit) 2 μ) atTop (𝓝 0) := by
  simp_rw [← smul_sub]
  exact L2_zero_smul _ constant hlimit

end
end Universality
