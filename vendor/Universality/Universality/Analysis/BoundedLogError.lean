import Universality.Analysis.NormalizedLogIteration

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem tendsto_ratio_of_bounded_error {α : Type*} (filter : Filter α) (first second : α → ℝ)
    (coefficient bound : ℝ) (hsecond : Tendsto second filter atBot)
    (herror : ∀ᶠ x in filter, |first x - coefficient * second x| ≤ bound) :
    Tendsto (fun x => first x / second x) filter (𝓝 coefficient) := by
  have hinverse : Tendsto (fun x => (second x)⁻¹) filter (𝓝 0) := tendsto_inv_atBot_zero.comp hsecond
  have hmajorant : Tendsto (fun x => bound * |(second x)⁻¹|) filter (𝓝 0) := by
    simpa using hinverse.abs.const_mul bound
  have hzero : Tendsto (fun x => (first x - coefficient * second x) / second x) filter (𝓝 0) := by
    apply squeeze_zero_norm' _ hmajorant
    filter_upwards [herror] with x hx
    rw [Real.norm_eq_abs, div_eq_mul_inv, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hnonzero : ∀ᶠ x in filter, second x ≠ 0 := by
    filter_upwards [hsecond.eventually (eventually_lt_atBot (0 : ℝ))] with x hx
    exact hx.ne
  have hresult := hzero.add_const coefficient
  simp only [zero_add] at hresult
  apply hresult.congr'
  filter_upwards [hnonzero] with x hx
  field_simp
  <;> ring

theorem tendsto_log_left_deviation (critical : ℝ) :
    Tendsto (fun p : ℝ => Real.log (critical - p)) (𝓝[<] critical) atBot := by
  have hbase : Tendsto (fun p : ℝ => critical - p) (𝓝[<] critical) (𝓝 0) := by
    have h : Tendsto (fun p : ℝ => critical - p) (𝓝 critical) (𝓝 (critical - critical)) :=
      tendsto_const_nhds.sub tendsto_id
    simpa only [sub_self] using h.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠ p in 𝓝[<] critical, critical - p ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    change p < critical at hp
    change 0 < critical - p
    exact sub_pos.mpr hp
  exact Real.tendsto_log_nhdsGT_zero.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase hpositive)

end
end Universality
