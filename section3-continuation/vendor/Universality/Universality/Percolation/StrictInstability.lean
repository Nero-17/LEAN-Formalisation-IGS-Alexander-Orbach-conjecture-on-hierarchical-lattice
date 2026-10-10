import Universality.Percolation.BernoulliVariance
import Universality.Percolation.StrictReliability

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem crossing_variance (p : ℝ) :
    bernoulliVariance p R.crossingIndicator = R.reliability p * (1 - R.reliability p) := by
  have hsquare : (fun ω => R.crossingIndicator ω ^ 2) = R.crossingIndicator := by
    funext ω
    simp only [crossingIndicator]
    cases R.crosses ω <;> norm_num
  rw [bernoulliVariance, hsquare, R.expectation_crossingIndicator]
  ring

theorem crossing_energy (p : ℝ) :
    bernoulliEnergy p R.crossingIndicator = deriv R.reliability p := by
  unfold bernoulliEnergy
  simp_rw [R.crossingIndicator_difference]
  have hsquare : ∀ ω edge, (if R.pivotal ω edge then (1 : ℝ) else 0) ^ 2 =
      (if R.pivotal ω edge then 1 else 0) := by
    intro ω edge
    cases R.pivotal ω edge <;> norm_num
  simp_rw [hsquare]
  rw [R.expectation_pivotalCount, ← R.russo_formula]

/-- The strict finite-product variance inequality gives a differential
crossing bound throughout the interval, not merely at a fixed point. -/
theorem strict_crossing_differential_inequality (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    R.reliability p * (1 - R.reliability p) < p * (1 - p) * deriv R.reliability p := by
  have h := strict_bernoulli_poincare hp hp' R.crossingIndicator
    (by simp [crossingIndicator, R.crosses_all_closed])
    (by intro edge; simp [crossingIndicator, R.crosses_onlyOpen_false_of_scale edge hscale])
    (by simp [crossingIndicator, (R.crosses_eq_true (fun _ => true)).mpr hconnected])
  rwa [R.crossing_variance, R.crossing_energy] at h

theorem interior_fixed_point_strictly_unstable (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : R.reliability p = p)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    1 < deriv R.reliability p := by
  have hconnected := (R.reliability_pos_iff_connected hp hp').mp (by rwa [hfixed])
  have h := R.strict_crossing_differential_inequality p hp hp' hconnected hscale
  rw [hfixed] at h
  have hpositive := mul_pos hp (sub_pos.mpr hp')
  exact (mul_lt_mul_iff_right₀ hpositive).mp (by simpa only [mul_one] using h)

end
end Universality.FiniteNetwork
