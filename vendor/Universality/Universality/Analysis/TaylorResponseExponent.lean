import Universality.Analysis.PowerResponseExponent
import Mathlib.Analysis.Calculus.Taylor

namespace Universality
noncomputable section
open Filter Set
open scoped Topology ContDiff

/-- The leading Taylor coefficient controls the normalized response on every
punctured filter approaching the expansion point. Only local finite regularity
is needed. -/
theorem taylor_leading_power_limit (response : ℝ → ℝ) (critical : ℝ) (order : ℕ)
    (filter : Filter ℝ) (hfilter : filter ≤ 𝓝 critical)
    (hnonzero : ∀ᶠ x in filter, x - critical ≠ 0)
    (hregular : ContDiffAt ℝ order response critical)
    (hvanish : ∀ i < order, iteratedDeriv i response critical = 0) :
    Tendsto (fun x => response x / (x - critical) ^ order) filter
      (𝓝 (iteratedDeriv order response critical / (order.factorial : ℝ))) := by
  obtain ⟨neighborhood, hneighborhood, hlocal⟩ :=
    hregular.contDiffOn (m := (order : ℕ∞ω)) le_rfl (by simp)
  obtain ⟨lower, upper, hcritical, hsubset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hneighborhood
  have hinterval := hlocal.mono hsubset
  have hwithin (i : ℕ) (hi : i ≤ order) :
      iteratedDerivWithin i response (Ioo lower upper) critical =
        iteratedDeriv i response critical :=
    iteratedDerivWithin_eq_iteratedDeriv isOpen_Ioo.uniqueDiffOn
      (hregular.of_le (by exact_mod_cast hi)) hcritical
  have hpolynomial (x : ℝ) :
      taylorWithinEval response order (Ioo lower upper) critical x =
        (iteratedDeriv order response critical / (order.factorial : ℝ)) *
          (x - critical) ^ order := by
    rw [taylor_within_apply, Finset.sum_eq_single order]
    · rw [hwithin order le_rfl]
      simp only [smul_eq_mul]
      ring
    · intro i hi hine
      have hilt : i < order := by
        have := Finset.mem_range.mp hi
        omega
      rw [hwithin i hilt.le, hvanish i hilt]
      simp
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _)))
  have htaylor := Real.taylor_tendsto (f := response) (n := order)
    (convex_Ioo lower upper) hcritical hinterval
  rw [nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds hcritical.1 hcritical.2)] at htaylor
  have hlimit := (htaylor.mono_left hfilter).add_const
    (iteratedDeriv order response critical / (order.factorial : ℝ))
  simp only [zero_add] at hlimit
  apply hlimit.congr'
  filter_upwards [hnonzero] with x hx
  rw [hpolynomial]
  field_simp
  <;> ring

/-- Both one-sided logarithmic orders and the required punctured nonvanishing
follow from the first nonzero derivative of a locally smooth response. -/
theorem two_sided_logarithmic_order_of_first_derivative
    (response : ℝ → ℝ) (critical : ℝ) (order : ℕ)
    (hregular : ContDiffAt ℝ order response critical)
    (hvanish : ∀ i < order, iteratedDeriv i response critical = 0)
    (hleading : iteratedDeriv order response critical ≠ 0) :
    ((∀ᶠ x in 𝓝[<] critical, response x ≠ 0) ∧
      Tendsto (fun x => Real.log |response x| / Real.log |x - critical|)
        (𝓝[<] critical) (𝓝 (order : ℝ))) ∧
    ((∀ᶠ x in 𝓝[>] critical, response x ≠ 0) ∧
      Tendsto (fun x => Real.log |response x| / Real.log |x - critical|)
        (𝓝[>] critical) (𝓝 (order : ℝ))) := by
  have hcoefficient : iteratedDeriv order response critical / (order.factorial : ℝ) ≠ 0 :=
    div_ne_zero hleading (by exact_mod_cast Nat.factorial_ne_zero order)
  have hleft : ∀ᶠ x in 𝓝[<] critical, x - critical ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (sub_neg.mpr hx).ne
  have hright : ∀ᶠ x in 𝓝[>] critical, x - critical ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (sub_pos.mpr hx).ne'
  constructor
  · exact logarithmic_order_of_power_asymptotic _ response (fun x => x - critical)
      order _ hcoefficient (tendsto_log_abs_deviation_left critical) hleft
      (taylor_leading_power_limit response critical order _ nhdsWithin_le_nhds
        hleft hregular hvanish)
  · exact logarithmic_order_of_power_asymptotic _ response (fun x => x - critical)
      order _ hcoefficient (tendsto_log_abs_deviation_right critical) hright
      (taylor_leading_power_limit response critical order _ nhdsWithin_le_nhds
        hright hregular hvanish)

end
end Universality
