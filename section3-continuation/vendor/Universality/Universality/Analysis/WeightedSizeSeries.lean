import Universality.Analysis.GeometricSizeKernel

namespace Universality
noncomputable section
set_option maxHeartbeats 0

theorem birth_size_weight_identity (edges growth coefficient : ℝ)
    (hedges : 0 < edges) (hgrowth : 0 < growth) (n : ℕ) :
    (1 / edges) ^ (n + 2) * (coefficient * (1 / growth) ^ n) =
      (coefficient / edges ^ 2) * (1 / (edges * growth)) ^ n := by
  simp only [pow_add, div_pow, one_pow, mul_pow]
  field_simp [hedges.ne', hgrowth.ne']
  <;> ring

/-- The exact shifted birth weights are retained. A polynomial pointwise
upper estimate and a single annular lower term give two-sided size bounds. -/
theorem weighted_size_series_bounds (birth : ℕ → ℝ) (edges growth size upper lower : ℝ)
    (hedges : 1 < edges) (hgrowth : 1 < growth) (order depth : ℕ)
    (horder : edges * growth < growth ^ order) (hsize : growth ^ depth ≤ size)
    (hupper : 0 ≤ upper) (hnonneg : ∀ n, 0 ≤ birth n)
    (hbound : ∀ n, birth n ≤ upper * (1 / growth) ^ n / (1 + size / growth ^ n) ^ order)
    (hlower : lower * (1 / growth) ^ depth ≤ birth depth) :
    Summable (fun n : ℕ => (1 / edges) ^ (n + 2) * birth n) ∧
      (lower / edges ^ 2) * (1 / (edges * growth)) ^ depth ≤
        (∑' n : ℕ, (1 / edges) ^ (n + 2) * birth n) ∧
      (∑' n : ℕ, (1 / edges) ^ (n + 2) * birth n) ≤
        ((upper / edges ^ 2) *
          ((1 - edges * growth / growth ^ order)⁻¹ + (1 - 1 / (edges * growth))⁻¹)) *
            (1 / (edges * growth)) ^ depth := by
  have hm : 0 < edges := zero_lt_one.trans hedges
  have hr : 0 < growth := zero_lt_one.trans hgrowth
  have hcoefficient : 0 ≤ upper / edges ^ 2 := div_nonneg hupper (pow_nonneg hm.le _)
  have hk := geometric_size_kernel_sum_bound edges growth hedges hgrowth order depth horder size hsize
  have hn (n : ℕ) : 0 ≤ (1 / edges) ^ (n + 2) * birth n :=
    mul_nonneg (pow_nonneg (one_div_nonneg.mpr hm.le) _) (hnonneg n)
  have hb (n : ℕ) : (1 / edges) ^ (n + 2) * birth n ≤
      (upper / edges ^ 2) * geometricSizeKernel edges growth order size n := by
    have hh := mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (one_div_nonneg.mpr hm.le) (n + 2))
    refine hh.trans_eq ?_
    rw [← mul_div_assoc, birth_size_weight_identity edges growth upper hm hr]
    simp only [geometricSizeKernel, mul_div_assoc]
  have hs := (hk.1.mul_left (upper / edges ^ 2)).of_nonneg_of_le hn hb
  refine ⟨hs, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hlower (pow_nonneg (one_div_nonneg.mpr hm.le) (depth + 2))
    rw [birth_size_weight_identity edges growth lower hm hr] at hh
    apply hh.trans
    simpa only [Finset.sum_singleton] using hs.sum_le_tsum {depth} (fun n _ => hn n)
  · have hh := hs.tsum_le_tsum hb (hk.1.mul_left (upper / edges ^ 2))
    rw [tsum_mul_left] at hh
    refine hh.trans ((mul_le_mul_of_nonneg_left hk.2 hcoefficient).trans_eq ?_)
    ring

end
end Universality
