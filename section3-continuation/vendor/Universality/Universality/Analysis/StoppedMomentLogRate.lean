import Universality.Analysis.GeometricSumLogRate
import Universality.Analysis.BoundedLogError

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem stopped_geometric_comparison_log_rate {α : Type*} (filter : Filter α)
    (response : α → ℝ) (depth : α → ℕ) (ratio lower upper : ℝ)
    (hdepth : Tendsto depth filter atTop) (hratio : 0 < ratio)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hcomparison : ∀ᶠ x in filter,
      lower * (∑ n ∈ Finset.range (depth x), ratio ^ (n + 1)) ≤ response x ∧
      response x ≤ upper * (∑ n ∈ Finset.range (depth x), ratio ^ (n + 1))) :
    Tendsto (fun x => Real.log (response x) / depth x) filter (𝓝 (max (Real.log ratio) 0)) := by
  have hsumLimit := (geometric_sum_log_rate ratio hratio).comp hdepth
  have hlowerLimit : Tendsto
      (fun x => Real.log lower / depth x + Real.log (∑ n ∈ Finset.range (depth x), ratio ^ (n + 1)) / depth x)
      filter (𝓝 (max (Real.log ratio) 0)) := by
    simpa only [zero_add, Function.comp_def] using
      ((tendsto_const_div_atTop_nhds_zero_nat (Real.log lower)).comp hdepth).add hsumLimit
  have hupperLimit : Tendsto
      (fun x => Real.log upper / depth x + Real.log (∑ n ∈ Finset.range (depth x), ratio ^ (n + 1)) / depth x)
      filter (𝓝 (max (Real.log ratio) 0)) := by
    simpa only [zero_add, Function.comp_def] using
      ((tendsto_const_div_atTop_nhds_zero_nat (Real.log upper)).comp hdepth).add hsumLimit
  have hpositive : ∀ᶠ x in filter, (0 : ℝ) < depth x ∧
      0 < ∑ n ∈ Finset.range (depth x), ratio ^ (n + 1) := by
    filter_upwards [hdepth.eventually (eventually_ge_atTop 1)] with x hx
    refine ⟨by exact_mod_cast (show 0 < depth x by omega), ?_⟩
    have hh := Finset.single_le_sum (s := Finset.range (depth x))
      (f := fun n => ratio ^ (n + 1)) (fun n _ => (pow_pos hratio _).le)
      (Finset.mem_range.mpr (show 0 < depth x by omega))
    exact hratio.trans_le (by simpa only [zero_add, pow_one] using hh)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerLimit hupperLimit
  · filter_upwards [hcomparison, hpositive] with x hx hp
    have hh := Real.log_le_log (mul_pos hlower hp.2) hx.1
    rw [Real.log_mul hlower.ne' hp.2.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh hp.1.le
  · filter_upwards [hcomparison, hpositive] with x hx hp
    have hh := Real.log_le_log ((mul_pos hlower hp.2).trans_le hx.1) hx.2
    rw [Real.log_mul hupper.ne' hp.2.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh hp.1.le

/-- The three geometric regimes pass through the same exact escape-time
estimate. The limiting coefficient includes the logarithmic boundary case. -/
theorem stopped_moment_logarithmic_exponent {α : Type*} (filter : Filter α)
    (response deviationLog : α → ℝ) (depth : α → ℕ)
    (ratio multiplier lower upper bound : ℝ)
    (hdepth : Tendsto depth filter atTop) (hdeviation : Tendsto deviationLog filter atBot)
    (hratio : 0 < ratio) (hmultiplier : 1 < multiplier)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hcomparison : ∀ᶠ x in filter,
      lower * (∑ n ∈ Finset.range (depth x), ratio ^ (n + 1)) ≤ response x ∧
      response x ≤ upper * (∑ n ∈ Finset.range (depth x), ratio ^ (n + 1)))
    (hescape : ∀ᶠ x in filter, |(depth x : ℝ) * Real.log multiplier + deviationLog x| ≤ bound) :
    Tendsto (fun x => Real.log (response x) / deviationLog x) filter
      (𝓝 (-max (Real.log ratio) 0 / Real.log multiplier)) := by
  have hlog : 0 < Real.log multiplier := Real.log_pos hmultiplier
  have hdepthRatio : Tendsto (fun x => (depth x : ℝ) / deviationLog x) filter
      (𝓝 (-1 / Real.log multiplier)) := by
    apply tendsto_ratio_of_bounded_error filter (fun x => (depth x : ℝ)) deviationLog
      (-1 / Real.log multiplier) (bound / Real.log multiplier) hdeviation
    filter_upwards [hescape] with x hx
    have heq : (depth x : ℝ) - (-1 / Real.log multiplier) * deviationLog x =
        ((depth x : ℝ) * Real.log multiplier + deviationLog x) / Real.log multiplier := by
      field_simp [hlog.ne']
      <;> ring
    rw [heq, abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right hx hlog.le
  have hresult := (stopped_geometric_comparison_log_rate filter response depth ratio lower upper
    hdepth hratio hlower hupper hcomparison).mul hdepthRatio
  have hlimit : max (Real.log ratio) 0 * (-1 / Real.log multiplier) =
      -max (Real.log ratio) 0 / Real.log multiplier := by ring
  rw [hlimit] at hresult
  apply hresult.congr'
  filter_upwards [hdepth.eventually (eventually_ge_atTop 1)] with x hx
  have hn : (depth x : ℝ) ≠ 0 := by exact_mod_cast (show depth x ≠ 0 by omega)
  exact div_mul_div_cancel₀ hn

end
end Universality
