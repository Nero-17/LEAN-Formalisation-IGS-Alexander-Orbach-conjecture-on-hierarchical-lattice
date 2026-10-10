import Universality.Matrix.PopulationGrowth

namespace Universality
noncomputable section
open Matrix Filter
open scoped Topology

theorem logarithmic_growth_of_eventual_bounds (population : ℕ → ℝ)
    (radius lower upper : ℝ) (hr : 0 < radius) (hl : 0 < lower) (hu : 0 < upper)
    (hbounds : ∀ᶠ n in atTop, lower * radius ^ n ≤ population n ∧
      population n ≤ upper * radius ^ n) :
    Tendsto (fun n : ℕ => Real.log (population n) / n) atTop (𝓝 (Real.log radius)) := by
  have hlower : Tendsto (fun n : ℕ => Real.log lower / n + Real.log radius)
      atTop (𝓝 (Real.log radius)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log lower)).add
      (tendsto_const_nhds (x := Real.log radius))
  have hupper : Tendsto (fun n : ℕ => Real.log upper / n + Real.log radius)
      atTop (𝓝 (Real.log radius)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log upper)).add
      (tendsto_const_nhds (x := Real.log radius))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop 0, hbounds] with n hn hb
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (mul_pos hl (pow_pos hr n)) hb.1
    rw [Real.log_mul hl.ne' (pow_ne_zero n hr.ne'), Real.log_pow] at hlog
    apply (le_div_iff₀ hn').mpr
    field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop 0, hbounds] with n hn hb
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hpositive := lt_of_lt_of_le (mul_pos hl (pow_pos hr n)) hb.1
    have hlog := Real.log_le_log hpositive hb.2
    rw [Real.log_mul hu.ne' (pow_ne_zero n hr.ne'), Real.log_pow] at hlog
    apply (div_le_iff₀ hn').mpr
    field_simp
    nlinarith

theorem matrix_column_power_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (j : ι) (lower upper : ℝ)
    (hM : ∀ i k, 0 ≤ M i k) (hcolumn : ∀ k, lower ≤ M k j ∧ M k j ≤ upper)
    (n : ℕ) (i : ι) :
    lower * (∑ k, (M ^ n) i k) ≤ (M ^ (n + 1)) i j ∧
      (M ^ (n + 1)) i j ≤ upper * (∑ k, (M ^ n) i k) := by
  rw [pow_succ, Matrix.mul_apply]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    simpa only [mul_comm lower] using
      mul_le_mul_of_nonneg_left (hcolumn k).1 (matrix_pow_nonneg M hM n i k)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    simpa only [mul_comm upper] using
      mul_le_mul_of_nonneg_left (hcolumn k).2 (matrix_pow_nonneg M hM n i k)

theorem matrix_entry_logarithmic_growth {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i) (hr : 0 < radius)
    (heigen : M *ᵥ weight = radius • weight) (i j : ι)
    (hcolumn : ∀ k, 0 < M k j) :
    Tendsto (fun n : ℕ => Real.log ((M ^ n) i j) / n)
      atTop (𝓝 (Real.log radius)) := by
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨jmin, _, hcmin⟩ := Finset.exists_min_image Finset.univ
    (fun k => M k j) Finset.univ_nonempty
  obtain ⟨jmax, _, hcmax⟩ := Finset.exists_max_image Finset.univ
    (fun k => M k j) Finset.univ_nonempty
  apply logarithmic_growth_of_eventual_bounds _ radius
    (M jmin j * (weight imin / weight imax) / radius)
    (M jmax j * (weight imax / weight imin) / radius) hr
    (div_pos (mul_pos (hcolumn _) (div_pos (hw _) (hw _))) hr)
    (div_pos (mul_pos (hcolumn _) (div_pos (hw _) (hw _))) hr)
  filter_upwards [eventually_gt_atTop 0] with n hn
  cases n with
  | zero => omega
  | succ n =>
    have hrows := row_sum_power_bounds M weight radius (weight imin) (weight imax)
      hM hr (hw _) (hw _)
      (fun k => ⟨hmin k (Finset.mem_univ k), hmax k (Finset.mem_univ k)⟩) heigen n i
    have hcols := matrix_column_power_bounds M j (M jmin j) (M jmax j) hM
      (fun k => ⟨hcmin k (Finset.mem_univ k), hcmax k (Finset.mem_univ k)⟩) n i
    have hl := mul_le_mul_of_nonneg_left hrows.1 (hcolumn jmin).le
    have hu := mul_le_mul_of_nonneg_left hrows.2 (hcolumn jmax).le
    constructor
    · convert hl.trans hcols.1 using 1 <;>
        first | rfl | (rw [pow_succ]; field_simp <;> ring)
    · convert hcols.2.trans hu using 1 <;>
        first | rfl | (rw [pow_succ]; field_simp <;> ring)

theorem matrix_entry_dimension {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (radius scale : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i) (hr : 0 < radius)
    (heigen : M *ᵥ weight = radius • weight) (i j : ι)
    (hcolumn : ∀ k, 0 < M k j) :
    Tendsto (fun n : ℕ => Real.log ((M ^ n) i j) / Real.log (scale ^ n))
      atTop (𝓝 (Real.log radius / Real.log scale)) := by
  simpa only [div_div, Real.log_pow] using
    (matrix_entry_logarithmic_growth M weight radius hM hw hr heigen i j hcolumn).div_const
      (Real.log scale)

end
end Universality
