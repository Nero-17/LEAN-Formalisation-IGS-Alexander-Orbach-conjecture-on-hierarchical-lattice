import Universality.Percolation.CriticalEscapeLocal

namespace Universality
noncomputable section

theorem finite_repelling_orbit_sum_bound (function : ℝ → ℝ) (center radius lower point : ℝ)
    (hlower : 1 < lower) (depth : ℕ)
    (hexpansion : ∀ q, |q - center| < radius → lower * |q - center| ≤ |function q - center|)
    (horbit : ∀ j ≤ depth, |function^[j] point - center| < radius) :
    (∑ j ∈ Finset.range (depth + 1), |function^[j] point - center|) ≤
      radius / (lower - 1) + radius := by
  have hgrowth := finite_growth_sum_bound (fun j => |function^[j] point - center|) lower depth
    (by
      intro j hj
      rw [Function.iterate_succ_apply']
      exact hexpansion _ (horbit j (by omega)))
  have hsum : (∑ j ∈ Finset.range depth, |function^[j] point - center|) ≤ radius / (lower - 1) := by
    apply (le_div_iff₀ (sub_pos.mpr hlower)).mpr
    have hend := horbit depth le_rfl
    have hstart := abs_nonneg (function^[0] point - center)
    nlinarith
  rw [Finset.sum_range_succ]
  exact add_le_add hsum (horbit depth le_rfl).le

namespace Rule
open Polynomial Filter
open scoped Topology

theorem Classical.local_reliability_distance_expansion {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ lower : ℝ, 1 < lower ∧ ∀ᶠ point in 𝓝 critical,
      lower * |point - critical| ≤ |rule.network.reliability point - critical| := by
  have hderivative : (rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)).derivative.eval critical =
      deriv rule.network.reliability critical := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, (rule.network.hasDerivAt_reliability critical).deriv]
  obtain ⟨quotient, lower, upper, rate, hlower, hrate, hfactor, hlocal⟩ :=
    polynomial_secant_local_bounds (rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)) critical
      (by rw [hderivative]; exact rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale)
  refine ⟨lower, hlower, ?_⟩
  filter_upwards [hlocal] with point hpoint
  have hidentity := hfactor point
  simp only [Polynomial.eval_map, FiniteNetwork.reliabilityPolynomial_eval, hfixed] at hidentity
  rw [hidentity, abs_mul, abs_of_nonneg ((zero_lt_one.trans hlower).le.trans hpoint.1)]
  exact (mul_le_mul_of_nonneg_right hpoint.1 (abs_nonneg _)).trans_eq (mul_comm _ _)

end Rule
end
end Universality
