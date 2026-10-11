import Universality.Percolation.MomentExitCompact
import Universality.Analysis.PolynomialEscapeBounds

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology

/-- The actual first-exit time has a uniformly bounded logarithmic error on
both sides of the critical point. The radius is chosen from the polynomial
secant estimate; no distortion estimate is assumed for the actual orbit. -/
theorem Classical.reliability_exit_log_bound {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ neighborhood : ℝ, 0 < neighborhood ∧ neighborhood < critical ∧ neighborhood < 1 - critical ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood →
        ∃ bound : ℝ, 0 ≤ bound ∧ ∀ p : ℝ, 0 < p → p < 1 → p ≠ critical →
          |(rule.reliabilityExitTime critical radius p : ℝ) * Real.log (deriv rule.network.reliability critical) +
            Real.log (|p - critical|)| ≤ bound := by
  let crossing : Polynomial ℝ := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  have hcrossing : crossing.eval = rule.network.reliability := by
    funext p
    simp only [crossing, Polynomial.eval_map, reliabilityPolynomial_eval]
  have hderivative : crossing.derivative.eval critical = deriv rule.network.reliability critical := by
    have h := (crossing.hasDerivAt critical).deriv
    rw [hcrossing] at h
    exact h.symm
  have hrepelling : 1 < crossing.derivative.eval critical := by
    rw [hderivative]
    exact rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale
  obtain ⟨quotient, lower, upper, rate, hlower, hrate, hfactor, hlocal⟩ :=
    polynomial_secant_local_bounds crossing critical hrepelling
  have hlowerGap : 0 < lower - 1 := sub_pos.mpr hlower
  obtain ⟨neighborhood, hneighborhood, hneighborhoodBound⟩ := Metric.eventually_nhds_iff.mp hlocal
  let cutoff := min neighborhood (min critical (1 - critical)) / 2
  have hminimum : 0 < min neighborhood (min critical (1 - critical)) :=
    lt_min hneighborhood (lt_min hc (sub_pos.mpr hc'))
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  have hcutoffNeighborhood : cutoff < neighborhood := by
    have h := min_le_left neighborhood (min critical (1 - critical))
    dsimp [cutoff]
    linarith
  have hcutoffCritical : cutoff < critical := by
    have h := (min_le_right neighborhood (min critical (1 - critical))).trans (min_le_left critical (1 - critical))
    dsimp [cutoff]
    linarith
  have hcutoffOne : cutoff < 1 - critical := by
    have h := (min_le_right neighborhood (min critical (1 - critical))).trans (min_le_right critical (1 - critical))
    dsimp [cutoff]
    linarith
  refine ⟨cutoff, hcutoff, hcutoffCritical, hcutoffOne, ?_⟩
  intro radius hradius hradiusCutoff
  have hradiusNeighborhood : radius < neighborhood := hradiusCutoff.trans_lt hcutoffNeighborhood
  have hradiusCritical : radius < critical := hradiusCutoff.trans_lt hcutoffCritical
  have hradiusOne : radius < 1 - critical := hradiusCutoff.trans_lt hcutoffOne
  refine ⟨|Real.log radius| + rate / (lower - 1), by positivity, ?_⟩
  intro p hp hp' hne
  have horbit (depth : ℕ) := h.reliability_orbit_interior_side critical p hc hc' hfixed hp hp' depth
  have horbitNe (depth : ℕ) : rule.network.reliability^[depth] p ≠ critical := by
    rcases lt_or_gt_of_ne hne with hbelow | habove
    · exact ((horbit depth).2.2.1 hbelow |>.trans_lt hbelow).ne
    · exact (habove.trans_le ((horbit depth).2.2.2 habove)).ne'
  have horbitPositive (depth : ℕ) : 0 < |rule.network.reliability^[depth] p - critical| :=
    abs_pos.mpr (sub_ne_zero.mpr (horbitNe depth))
  have horbitBound (depth : ℕ) : |rule.network.reliability^[depth] p - critical| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [(horbit depth).1, (horbit depth).2.1]
  have hbefore (depth : ℕ) (hdepth : depth < rule.reliabilityExitTime critical radius p) :
      lower ≤ quotient.eval (rule.network.reliability^[depth] p) ∧
        quotient.eval (rule.network.reliability^[depth] p) ≤ upper ∧
          |Real.log (quotient.eval (rule.network.reliability^[depth] p)) -
              Real.log (crossing.derivative.eval critical)| ≤
            rate * |rule.network.reliability^[depth] p - critical| := by
    apply hneighborhoodBound
    rw [Real.dist_eq]
    exact (h.reliability_exit_before critical radius p hc hc' hfixed hradiusCritical hradiusOne
      hp hp' hne depth hdepth).trans hradiusNeighborhood
  have hstepIdentity (depth : ℕ) (hdepth : depth < rule.reliabilityExitTime critical radius p) :
      |rule.network.reliability^[depth + 1] p - critical| =
        |rule.network.reliability^[depth] p - critical| * quotient.eval (rule.network.reliability^[depth] p) := by
    have hquotientPositive : 0 < quotient.eval (rule.network.reliability^[depth] p) :=
      (zero_lt_one.trans hlower).trans_le (hbefore depth hdepth).1
    have h := hfactor (rule.network.reliability^[depth] p)
    rw [congrFun hcrossing (rule.network.reliability^[depth] p),
      congrFun hcrossing critical, hfixed] at h
    rw [Function.iterate_succ_apply', h, abs_mul, abs_of_pos hquotientPositive]
  have herror := finite_escape_time_error_bound
    (fun depth => |rule.network.reliability^[depth] p - critical|)
    (deriv rule.network.reliability critical) lower rate (rule.reliabilityExitTime critical radius p)
    hlower hrate.le (abs_nonneg _) (by
      intro depth hdepth
      rw [hstepIdentity depth hdepth]
      exact (mul_comm lower _).trans_le
        (mul_le_mul_of_nonneg_left (hbefore depth hdepth).1 (abs_nonneg _)))
    (by
      intro depth hdepth
      have hquotientPositive : 0 < quotient.eval (rule.network.reliability^[depth] p) :=
        (zero_lt_one.trans hlower).trans_le (hbefore depth hdepth).1
      rw [hstepIdentity depth hdepth,
        Real.log_mul (horbitPositive depth).ne' hquotientPositive.ne']
      have hbound := (hbefore depth hdepth).2.2
      rw [hderivative] at hbound
      convert hbound using 1 <;> congr 1 <;> ring)
  have hafter := h.reliability_exit_spec critical radius p hc hc' hfixed hradiusCritical hradiusOne hp hp' hne
  have hlogLower := Real.log_le_log hradius hafter
  have hlogUpper := Real.log_nonpos (abs_nonneg
    (rule.network.reliability^[rule.reliabilityExitTime critical radius p] p - critical)) (horbitBound _)
  have hlogBound : |Real.log (|rule.network.reliability^[rule.reliabilityExitTime critical radius p] p - critical|)| ≤
      |Real.log radius| := abs_le.mpr
    ⟨(neg_abs_le (Real.log radius)).trans hlogLower, hlogUpper.trans (abs_nonneg _)⟩
  have hrateBound : rate * |rule.network.reliability^[rule.reliabilityExitTime critical radius p] p - critical| /
      (lower - 1) ≤ rate / (lower - 1) := by
    apply div_le_div_of_nonneg_right ?_ (sub_nonneg.mpr hlower.le)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (horbitBound _) hrate.le
  exact herror.trans (add_le_add hlogBound hrateBound)

end
end Universality.Rule

