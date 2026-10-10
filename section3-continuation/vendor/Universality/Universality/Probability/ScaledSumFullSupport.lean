import Universality.Probability.ScaledSumSupportGrid

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem exists_sequence_crossing_bound (sequence : ℕ → ℝ) (ratio threshold : ℝ)
    (hzero : 0 ≤ sequence 0) (hratio : 0 ≤ ratio) (hthreshold : 0 < threshold)
    (hunbounded : Tendsto sequence atTop atTop)
    (hstep : ∀ n, sequence (n + 1) ≤ ratio * sequence n) :
    ∃ n : ℕ, threshold ≤ sequence n ∧ sequence n ≤ sequence 0 + ratio * threshold := by
  classical
  have hexists : ∃ n : ℕ, threshold ≤ sequence n :=
    (hunbounded.eventually (eventually_ge_atTop threshold)).exists
  let n := Nat.find hexists
  refine ⟨n, Nat.find_spec hexists, ?_⟩
  by_cases hn : n = 0
  · rw [hn]
    nlinarith
  · have hprevious : sequence (n - 1) < threshold := by
      exact lt_of_not_ge (Nat.find_min hexists (by omega : n - 1 < n))
    have hnext := hstep (n - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hnext
    exact hnext.trans ((mul_le_mul_of_nonneg_left hprevious.le hratio).trans (by linarith))

/-- A closed support, closed under scaled d-fold sums, is the whole positive
half-line once it contains zero and an unbounded sequence with bounded ratios. -/
theorem scaled_sum_full_positive_support (support : Set ℝ) (degree : ℕ) (radius ratio : ℝ)
    (hclosed : IsClosed support) (hdegree : 2 ≤ degree) (hradius : (degree : ℝ) < radius)
    (hratio : 0 ≤ ratio) (hzero : 0 ∈ support)
    (hsum : ∀ value : Fin degree → ℝ,
      (∀ i, value i ∈ support) → (∑ i, value i) / radius ∈ support)
    (sequence : ℕ → ℝ) (hsequence : ∀ n, sequence n ∈ support)
    (hsequence0 : 0 ≤ sequence 0) (hunbounded : Tendsto sequence atTop atTop)
    (hstep : ∀ n, sequence (n + 1) ≤ ratio * sequence n)
    (x : ℝ) (hx : 0 < x) : x ∈ support := by
  have hdegree1 : 1 < (degree : ℝ) := by exact_mod_cast (show 1 < degree by omega)
  have hradius1 : 1 < radius := hdegree1.trans hradius
  have hradius0 : 0 < radius := zero_lt_one.trans hradius1
  have hdegree0 : 0 < (degree : ℝ) := zero_lt_one.trans hdegree1
  have hinverseRadius := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hradius1)
  have hinverseDegree := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hdegree1)
  have hmeshLimit : Tendsto (fun k : ℕ => sequence 0 / radius ^ k + ratio * x / (degree : ℝ) ^ k)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, zero_add] using
      (hinverseRadius.const_mul (sequence 0)).add (hinverseDegree.const_mul (ratio * x))
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro error herror
  obtain ⟨k, hk⟩ := (hmeshLimit.eventually (gt_mem_nhds herror)).exists
  have hpowerRadius : 0 < radius ^ k := pow_pos hradius0 _
  have hpowerDegree : 0 < (degree : ℝ) ^ k := pow_pos hdegree0 _
  obtain ⟨n, hnLower, hnUpper⟩ := exists_sequence_crossing_bound sequence ratio
    (x * radius ^ k / (degree : ℝ) ^ k) hsequence0 hratio
    (div_pos (mul_pos hx hpowerRadius) hpowerDegree) hunbounded hstep
  have hnPos : 0 < sequence n := (div_pos (mul_pos hx hpowerRadius) hpowerDegree).trans_le hnLower
  let count := Nat.floor (x * radius ^ k / sequence n)
  have hcount : count ≤ degree ^ k := by
    apply Nat.floor_le_of_le
    rw [Nat.cast_pow]
    apply (div_le_iff₀ hnPos).mpr
    have := (div_le_iff₀ hpowerDegree).mp hnLower
    nlinarith
  have hgrid := scaled_sum_support_grid support degree radius hradius0 hzero hsum
    (sequence n) (hsequence n) k count hcount
  refine ⟨(count : ℝ) * sequence n / radius ^ k, hgrid, ?_⟩
  have hfloor := Nat.floor_le (div_nonneg (mul_pos hx hpowerRadius).le hnPos.le)
  have hgridLe : (count : ℝ) * sequence n / radius ^ k ≤ x := by
    apply (div_le_iff₀ hpowerRadius).mpr
    have := (le_div_iff₀ hnPos).mp hfloor
    exact this
  have hfloorUpper := Nat.lt_floor_add_one (x * radius ^ k / sequence n)
  have herrorMesh : x - (count : ℝ) * sequence n / radius ^ k < sequence n / radius ^ k := by
    apply (lt_div_iff₀ hpowerRadius).mpr
    rw [sub_mul, div_mul_cancel₀ _ hpowerRadius.ne']
    have := (div_lt_iff₀ hnPos).mp hfloorUpper
    nlinarith
  have hmeshBound : sequence n / radius ^ k ≤
      sequence 0 / radius ^ k + ratio * x / (degree : ℝ) ^ k := by
    calc
      sequence n / radius ^ k ≤
          (sequence 0 + ratio * (x * radius ^ k / (degree : ℝ) ^ k)) / radius ^ k :=
        div_le_div_of_nonneg_right hnUpper hpowerRadius.le
      _ = _ := by field_simp
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hgridLe)]
  exact herrorMesh.trans_le hmeshBound |>.trans hk

end
end Universality
