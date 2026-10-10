import Universality.Analysis.TwoSidedGeometricCutoff

namespace Universality
noncomputable section
set_option maxHeartbeats 0

def geometricSizeKernel (edges growth : ℝ) (order : ℕ) (size : ℝ) (generation : ℕ) : ℝ :=
  (1 / (edges * growth)) ^ generation / (1 + size / growth ^ generation) ^ order

theorem geometric_size_kernel_reverse_identity (edges growth : ℝ)
    (hedges : 0 < edges) (hgrowth : 0 < growth) (order generation distance : ℕ) :
    (1 / (edges * growth)) ^ generation / (growth ^ distance) ^ order =
      (1 / (edges * growth)) ^ (generation + distance) * (edges * growth / growth ^ order) ^ distance := by
  have hswap : (growth ^ distance) ^ order = (growth ^ order) ^ distance := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm distance order]
  rw [hswap]
  simp only [pow_add, div_pow, one_pow, mul_pow]
  field_simp [hedges.ne', hgrowth.ne']

theorem geometric_size_kernel_sum_bound (edges growth : ℝ)
    (hedges : 1 < edges) (hgrowth : 1 < growth) (order depth : ℕ)
    (horder : edges * growth < growth ^ order) (size : ℝ) (hsize : growth ^ depth ≤ size) :
    Summable (geometricSizeKernel edges growth order size) ∧
      (∑' n : ℕ, geometricSizeKernel edges growth order size n) ≤
        (1 / (edges * growth)) ^ depth *
          ((1 - edges * growth / growth ^ order)⁻¹ + (1 - 1 / (edges * growth))⁻¹) := by
  have hm : 0 < edges := zero_lt_one.trans hedges
  have hr : 0 < growth := zero_lt_one.trans hgrowth
  have hsizePos : 0 < size := (pow_pos hr _).trans_le hsize
  have hproduct : 1 < edges * growth :=
    hedges.trans_le (le_mul_of_one_le_right hm.le hgrowth.le)
  have hscale : 0 < 1 / (edges * growth) := one_div_pos.mpr (mul_pos hm hr)
  have hscaleOne : 1 / (edges * growth) < 1 := (div_lt_one (mul_pos hm hr)).mpr hproduct
  have hfirst : 0 ≤ edges * growth / growth ^ order := div_nonneg (mul_nonneg hm.le hr.le) (pow_nonneg hr.le _)
  have hfirstOne : edges * growth / growth ^ order < 1 := (div_lt_one (pow_pos hr _)).mpr horder
  have hnonneg (n : ℕ) : 0 ≤ geometricSizeKernel edges growth order size n :=
    div_nonneg (pow_nonneg hscale.le _) (pow_nonneg (by positivity) _)
  have hpre (n : ℕ) (hn : n ≤ depth) : geometricSizeKernel edges growth order size n ≤
      1 * (1 / (edges * growth)) ^ depth * (edges * growth / growth ^ order) ^ (depth - n) := by
    have hsum : n + (depth - n) = depth := by omega
    have hbase : growth ^ (depth - n) ≤ size / growth ^ n := by
      apply (le_div_iff₀ (pow_pos hr _)).mpr
      calc
        _ = growth ^ depth := by rw [mul_comm, ← pow_add, hsum]
        _ ≤ size := hsize
    have hdenominator : growth ^ (depth - n) ≤ 1 + size / growth ^ n := by linarith
    have hb := div_le_div_of_nonneg_left (pow_nonneg hscale.le n)
      (pow_pos (pow_pos hr (depth - n)) order)
      (pow_le_pow_left₀ (pow_nonneg hr.le _) hdenominator order)
    have heq := geometric_size_kernel_reverse_identity edges growth hm hr order n (depth - n)
    rw [hsum] at heq
    change (1 / (edges * growth)) ^ n / (1 + size / growth ^ n) ^ order ≤
      1 * (1 / (edges * growth)) ^ depth * (edges * growth / growth ^ order) ^ (depth - n)
    rw [one_mul]
    exact hb.trans_eq heq
  have hpost (j : ℕ) : geometricSizeKernel edges growth order size (depth + 1 + j) ≤
      1 * (1 / (edges * growth)) ^ depth * (1 / (edges * growth)) ^ j := by
    have hdenominator : 1 ≤ (1 + size / growth ^ (depth + 1 + j)) ^ order :=
      one_le_pow₀ (by have := div_nonneg hsizePos.le (pow_nonneg hr.le (depth + 1 + j)); linarith)
    calc
      _ ≤ (1 / (edges * growth)) ^ (depth + 1 + j) :=
        div_le_self (pow_nonneg hscale.le _) hdenominator
      _ = ((1 / (edges * growth)) ^ depth * (1 / (edges * growth)) ^ j) * (1 / (edges * growth)) := by
        rw [pow_add, pow_add, pow_one]
        ring
      _ ≤ (1 / (edges * growth)) ^ depth * (1 / (edges * growth)) ^ j :=
        mul_le_of_le_one_right (mul_nonneg (pow_nonneg hscale.le _) (pow_nonneg hscale.le _)) hscaleOne.le
      _ = _ := by rw [one_mul]
  simpa only [one_mul] using two_sided_geometric_cutoff_sum
    (geometricSizeKernel edges growth order size) (1 / (edges * growth))
    (edges * growth / growth ^ order) (1 / (edges * growth)) 1 depth hscale.le hfirst hfirstOne
    hscale.le hscaleOne zero_le_one hnonneg hpre hpost

end
end Universality
