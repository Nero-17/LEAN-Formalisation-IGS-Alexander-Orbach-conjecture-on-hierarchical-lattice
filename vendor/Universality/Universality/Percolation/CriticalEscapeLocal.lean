import Universality.Analysis.PolynomialEscapeBounds
import Universality.Percolation.CrossingLengthContinuity

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open FiniteNetwork Polynomial

theorem Classical.subcritical_local_escape_bounds {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius lower upper rate : ℝ, 0 < radius ∧ 1 < lower ∧ 0 < rate ∧ 1 < upper ∧
      ∀ point, point < critical → critical - point < radius →
        lower * (critical - point) ≤ critical - rule.network.reliability point ∧
        critical - rule.network.reliability point ≤ upper * (critical - point) ∧
        |Real.log (critical - rule.network.reliability point) - Real.log (critical - point) -
          Real.log (deriv rule.network.reliability critical)| ≤ rate * (critical - point) := by
  have hderivative : (rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)).derivative.eval critical =
      deriv rule.network.reliability critical := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, (rule.network.hasDerivAt_reliability critical).deriv]
  obtain ⟨quotient, lower, upper, rate, hlower, hrate, hfactor, hlocal⟩ :=
    polynomial_secant_local_bounds (rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)) critical
      (by rw [hderivative]; exact rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale)
  obtain ⟨radius, hradius, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hcenter := hball (y := critical) (by simpa using hradius)
  refine ⟨radius, lower, upper, rate, hradius, hlower, hrate,
    hlower.trans_le (hcenter.1.trans hcenter.2.1), ?_⟩
  intro point hpoint hdistance
  have hdelta : 0 < critical - point := sub_pos.mpr hpoint
  have hnorm : |point - critical| = critical - point := abs_of_neg (sub_neg.mpr hpoint) |>.trans (by ring)
  have hbounds := hball (y := point) (by simpa only [Real.dist_eq, hnorm] using hdistance)
  have hquotient : 0 < quotient.eval point := (lt_trans zero_lt_one hlower).trans_le hbounds.1
  have hidentity : critical - rule.network.reliability point = (critical - point) * quotient.eval point := by
    have hidentity := hfactor point
    simp only [Polynomial.eval_map, reliabilityPolynomial_eval, hfixed] at hidentity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hidentity, mul_comm (critical - point)]
    exact mul_le_mul_of_nonneg_right hbounds.1 hdelta.le
  · rw [hidentity, mul_comm (critical - point)]
    exact mul_le_mul_of_nonneg_right hbounds.2.1 hdelta.le
  · rw [hidentity, Real.log_mul hdelta.ne' hquotient.ne']
    have hlog := hbounds.2.2
    rw [hderivative, hnorm] at hlog
    convert hlog using 1 <;> congr 1 <;> ring

end
end Universality.Rule
