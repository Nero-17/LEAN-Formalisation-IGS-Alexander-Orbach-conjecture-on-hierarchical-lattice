import Universality.Probability.FourthMomentConvergence
import Universality.Analysis.NormalizedGeometricSum
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem geometric_L2_sum_tendsto_zero (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (bound rate radius : ℝ) (hbound : 0 ≤ bound) (hrate : 0 ≤ rate)
    (hradius : 1 < radius) (hgap : rate < radius)
    (hestimate : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (bound * rate ^ n)) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => (∑ k ∈ Finset.range n, f k x) / radius ^ n) 2 μ)
      atTop (𝓝 0) := by
  have hpositive : 0 < radius := lt_trans zero_lt_one hradius
  have hsum (n : ℕ) : eLpNorm (∑ k ∈ Finset.range n, f k) 2 μ ≤
      ENNReal.ofReal (bound * ∑ k ∈ Finset.range (n + 1), rate ^ k) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, eLpNorm (f k) 2 μ :=
        eLpNorm_sum_le (fun k _ => (hf k).aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (bound * rate ^ k) :=
        Finset.sum_le_sum (fun k _ => hestimate k)
      _ = ENNReal.ofReal (bound * ∑ k ∈ Finset.range n, rate ^ k) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hbound (pow_nonneg hrate k)),
          Finset.mul_sum]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.sum_range_succ, mul_add]
        exact le_add_of_nonneg_right (mul_nonneg hbound (pow_nonneg hrate n))
  have hnormalized (n : ℕ) : eLpNorm (fun x => (∑ k ∈ Finset.range n, f k x) / radius ^ n) 2 μ ≤
      ENNReal.ofReal (bound * ((∑ k ∈ Finset.range (n + 1), rate ^ k) / radius ^ n)) := by
    have heq : (fun x => (∑ k ∈ Finset.range n, f k x) / radius ^ n) =
        (radius ^ n)⁻¹ • (∑ k ∈ Finset.range n, f k) := by
      funext x
      simp [div_eq_mul_inv, mul_comm]
    rw [heq, eLpNorm_const_smul, Real.enorm_of_nonneg (inv_nonneg.mpr (pow_nonneg hpositive.le n))]
    apply (mul_le_mul_left' (hsum n) _).trans_eq
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hpositive.le n))]
    congr 1
    ring
  have hlimit := (ENNReal.continuous_ofReal.tendsto (bound * 0)).comp
    ((normalized_geometric_sum_subcritical radius rate hradius
      (by rwa [abs_of_nonneg hrate])).const_mul bound)
  simp only [mul_zero, ENNReal.ofReal_zero] at hlimit
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimit
    (fun _ => bot_le) hnormalized

theorem geometric_second_moment_sum_tendsto_zero (f : ℕ → Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (bound radius : ℝ) (hbound : 0 ≤ bound)
    (hradius : 1 < radius) (hestimate : ∀ n, ∫ x, f n x ^ 2 ∂μ ≤ bound * radius ^ n) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => (∑ k ∈ Finset.range n, f k x) / radius ^ n) 2 μ)
      atTop (𝓝 0) := by
  have hpositive : 0 < radius := lt_trans zero_lt_one hradius
  apply geometric_L2_sum_tendsto_zero f hf (Real.sqrt bound) (Real.sqrt radius) radius
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hradius
    (by nlinarith [Real.sq_sqrt hpositive.le, Real.sqrt_nonneg radius])
  intro n
  apply eLpNorm_two_le_of_integral_sq_le (hf n)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) n))
  have heq : (Real.sqrt bound * Real.sqrt radius ^ n) ^ 2 = bound * radius ^ n := by
    rw [mul_pow, Real.sq_sqrt hbound, ← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt hpositive.le]
  rw [heq]
  exact hestimate n

end
end Universality
