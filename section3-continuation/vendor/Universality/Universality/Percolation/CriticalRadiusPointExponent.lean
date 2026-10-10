import Universality.Analysis.RadiusPointExponent
import Universality.Percolation.RadiusPointLaw
import Universality.Percolation.CriticalRadiusPowerBounds

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

theorem Classical.critical_radius_point_exponent_if_exists {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (exponent : ℝ)
    (hpositive : ∀ᶠ radius : ℕ in atTop, 0 < rule.limitingRootRadiusProbability p radius)
    (hlimit : Tendsto (fun radius : ℕ => Real.log (rule.limitingRootRadiusProbability p radius) /
      Real.log (radius : ℝ)) atTop (𝓝 exponent)) :
    exponent = -1 - (Real.log (rule.edges : ℝ) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
  have hgrowth : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) (h.terminal_degree_spectral_bounds p hp hp').2.1
  have hgap := Real.log_lt_log hgrowth (h.mass_spectralRadius_lt_edges p hp hp')
  have hscale : 0 < Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < rule.network.fullGraph.dist rule.network.source rule.network.target by have := h.scale; omega))
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := h.critical_radius_power_bounds p hp hp' hfixed
  have hh := point_log_limit_eq_of_tail_power_bounds
    (rule.limitingRootRadiusProbability p) (rule.limitingRootRadiusTailProbability p)
    (rule.limitingRootRadiusProbability_partial_sum p)
    (rule.limitingRootRadiusTailProbability_nonneg h.edges_gt_one h.vertices_gt_two hp.le hp'.le)
    (h.limitingRootRadiusTailProbability_tendsto_zero hp.le hp'.le)
    _ lower upper (div_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hgap)) hscale)
    hlower hupper hbounds exponent hpositive hlimit
  convert hh using 1 <;> ring

end
end Universality.Rule
