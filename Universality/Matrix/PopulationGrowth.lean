import Universality.Matrix.CommonPositiveVector
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Growth of a nonnegative mass recursion

A positive eigenvector bounds every row sum of every matrix power by fixed
positive multiples of the Perron growth.  Consequently the logarithmic growth
limit exists.  Application to random clusters additionally needs the theorem
identifying their first moments with these matrix iterates.
-/

namespace Universality
noncomputable section
open Matrix Filter
open scoped Topology

theorem matrix_pow_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) (n : ℕ) :
    ∀ i j, 0 ≤ (M ^ n) i j := by
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hM k j))

theorem row_sum_power_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius lower upper : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hr : 0 < radius) (hl : 0 < lower) (hu : 0 < upper)
    (hweight : ∀ i, lower ≤ weight i ∧ weight i ≤ upper)
    (heigen : M *ᵥ weight = radius • weight) (n : ℕ) (i : ι) :
    (lower / upper) * radius ^ n ≤ ∑ j, (M ^ n) i j ∧
      (∑ j, (M ^ n) i j) ≤ (upper / lower) * radius ^ n := by
  have hpower := congrFun (common_eigenvector_pow M weight radius heigen n) i
  change (∑ j, (M ^ n) i j * weight j) = radius ^ n * weight i at hpower
  have hlow : lower * (∑ j, (M ^ n) i j) ≤ radius ^ n * weight i := by
    rw [← hpower, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_comm lower] using
      mul_le_mul_of_nonneg_left (hweight j).1 (matrix_pow_nonneg M hM n i j)
  have hupp : radius ^ n * weight i ≤ upper * (∑ j, (M ^ n) i j) := by
    rw [← hpower, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_comm upper] using
      mul_le_mul_of_nonneg_left (hweight j).2 (matrix_pow_nonneg M hM n i j)
  constructor
  · apply (le_of_mul_le_mul_left (a := upper) · hu)
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (hweight i).1 (pow_pos hr n).le]
  · apply (le_of_mul_le_mul_left (a := lower) · hl)
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (hweight i).2 (pow_pos hr n).le]

theorem logarithmic_growth_of_bounds (population : ℕ → ℝ) (radius lower upper : ℝ)
    (hr : 0 < radius) (hl : 0 < lower) (hu : 0 < upper)
    (hbounds : ∀ n, lower * radius ^ n ≤ population n ∧
      population n ≤ upper * radius ^ n) :
    Tendsto (fun n : ℕ => Real.log (population n) / n) atTop (𝓝 (Real.log radius)) := by
  have hpopulation (n : ℕ) : 0 < population n :=
    lt_of_lt_of_le (mul_pos hl (pow_pos hr n)) (hbounds n).1
  have hlower : Tendsto (fun n : ℕ => Real.log lower / n + Real.log radius)
      atTop (𝓝 (Real.log radius)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log lower)).add
      (tendsto_const_nhds (x := Real.log radius))
  have hupper : Tendsto (fun n : ℕ => Real.log upper / n + Real.log radius)
      atTop (𝓝 (Real.log radius)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log upper)).add
      (tendsto_const_nhds (x := Real.log radius))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (mul_pos hl (pow_pos hr n)) (hbounds n).1
    rw [Real.log_mul hl.ne' (pow_ne_zero n hr.ne'), Real.log_pow] at hlog
    apply (le_div_iff₀ hn').mpr
    field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (hpopulation n) (hbounds n).2
    rw [Real.log_mul hu.ne' (pow_ne_zero n hr.ne'), Real.log_pow] at hlog
    apply (div_le_iff₀ hn').mpr
    field_simp
    nlinarith

theorem matrix_row_sum_logarithmic_growth {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i) (hr : 0 < radius)
    (heigen : M *ᵥ weight = radius • weight) (i : ι) :
    Tendsto (fun n : ℕ => Real.log (∑ j, (M ^ n) i j) / n)
      atTop (𝓝 (Real.log radius)) := by
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  apply logarithmic_growth_of_bounds _ radius
    (weight imin / weight imax) (weight imax / weight imin) hr
    (div_pos (hw imin) (hw imax)) (div_pos (hw imax) (hw imin))
  intro n
  apply row_sum_power_bounds M weight radius (weight imin) (weight imax)
    hM hr (hw imin) (hw imax) _ heigen n i
  intro j
  exact ⟨hmin j (Finset.mem_univ j), hmax j (Finset.mem_univ j)⟩

theorem matrix_row_sum_dimension {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius scale : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i) (hr : 0 < radius)
    (heigen : M *ᵥ weight = radius • weight) (i : ι) :
    Tendsto (fun n : ℕ => Real.log (∑ j, (M ^ n) i j) / Real.log (scale ^ n))
      atTop (𝓝 (Real.log radius / Real.log scale)) := by
  simpa only [div_div, Real.log_pow] using
    (matrix_row_sum_logarithmic_growth M weight radius hM hw hr heigen i).div_const
      (Real.log scale)

end
end Universality
