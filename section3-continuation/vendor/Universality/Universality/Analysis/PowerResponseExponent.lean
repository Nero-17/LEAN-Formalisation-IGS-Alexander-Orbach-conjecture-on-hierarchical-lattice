import Universality.Analysis.BoundedLogError

namespace Universality
noncomputable section
open Filter
open scoped Topology

/-- A nonzero leading power determines the logarithmic response exponent.
The hypothesis is a genuine asymptotic expansion; no physical density regularity
is asserted by this abstract conversion lemma. -/
theorem logarithmic_order_of_power_asymptotic {ι : Type*} (filter : Filter ι)
    (response deviation : ι → ℝ) (order : ℕ) (coefficient : ℝ)
    (hcoefficient : coefficient ≠ 0)
    (hdeviation : Tendsto (fun x => Real.log |deviation x|) filter atBot)
    (hnonzero : ∀ᶠ x in filter, deviation x ≠ 0)
    (hresponse : Tendsto (fun x => response x / deviation x ^ order) filter (𝓝 coefficient)) :
    (∀ᶠ x in filter, response x ≠ 0) ∧
      Tendsto (fun x => Real.log |response x| / Real.log |deviation x|)
        filter (𝓝 (order : ℝ)) := by
  have hnormalized : ∀ᶠ x in filter, response x / deviation x ^ order ≠ 0 :=
    hresponse.eventually (eventually_ne_nhds hcoefficient)
  have hresponse_nonzero : ∀ᶠ x in filter, response x ≠ 0 := by
    filter_upwards [hnormalized] with x hx
    exact (div_ne_zero_iff.mp hx).1
  refine ⟨hresponse_nonzero, ?_⟩
  have hlog : Tendsto (fun x => Real.log |response x / deviation x ^ order|)
      filter (𝓝 (Real.log |coefficient|)) :=
    (Real.continuousAt_log (abs_ne_zero.mpr hcoefficient)).tendsto.comp hresponse.abs
  have herror : Tendsto (fun x => Real.log |response x / deviation x ^ order| /
      Real.log |deviation x|) filter (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      hlog.mul (tendsto_inv_atBot_zero.comp hdeviation)
  have hlognonzero : ∀ᶠ x in filter, Real.log |deviation x| ≠ 0 := by
    filter_upwards [hdeviation.eventually (eventually_lt_atBot (0 : ℝ))] with x hx
    exact hx.ne
  have hlimit := herror.add_const (order : ℝ)
  simp only [zero_add] at hlimit
  apply hlimit.congr'
  filter_upwards [hresponse_nonzero, hnonzero, hlognonzero] with x hx hd hl
  rw [abs_div, abs_pow, Real.log_div (abs_ne_zero.mpr hx)
    (pow_ne_zero _ (abs_ne_zero.mpr hd)), Real.log_pow]
  field_simp
  <;> ring

theorem tendsto_log_abs_deviation_left (critical : ℝ) :
    Tendsto (fun p : ℝ => Real.log |p - critical|) (𝓝[<] critical) atBot := by
  apply (tendsto_log_left_deviation critical).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  change p < critical at hp
  rw [abs_of_neg (sub_neg.mpr hp)]
  congr 1
  ring

theorem tendsto_log_abs_deviation_right (critical : ℝ) :
    Tendsto (fun p : ℝ => Real.log |p - critical|) (𝓝[>] critical) atBot := by
  have hbase : Tendsto (fun p : ℝ => p - critical) (𝓝[>] critical) (𝓝 0) := by
    have h : Tendsto (fun p : ℝ => p - critical) (𝓝 critical) (𝓝 (critical - critical)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa only [sub_self] using h.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠ p in 𝓝[>] critical, p - critical ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    change critical < p at hp
    change 0 < p - critical
    exact sub_pos.mpr hp
  have h := Real.tendsto_log_nhdsGT_zero.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase hpositive)
  apply h.congr'
  filter_upwards [hpositive] with p hp
  rw [abs_of_pos hp]
  rfl

end
end Universality
