import Universality.Percolation.RadiusGeometricLower
import Universality.Percolation.RadiusGeometricUpper
import Universality.Analysis.RadiusGeometricInterpolation
import Universality.Analysis.PowerBoundsFromLogError
import Universality.Percolation.MassSpectralLowerBound

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter

theorem Classical.critical_radius_power_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ radius : ℕ in atTop,
      lower * (radius : ℝ) ^ (-(Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) ≤
        rule.limitingRootRadiusTailProbability p radius ∧
      rule.limitingRootRadiusTailProbability p radius ≤
        upper * (radius : ℝ) ^ (-(Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by
  obtain ⟨lower, hlower, hlowerBound⟩ := h.radius_tail_geometric_lower p hp hp' hfixed
  obtain ⟨bound, hbound, upper, hupper, hupperBound⟩ := h.radius_tail_geometric_upper p hp hp' hfixed
  have hm : (0 : ℝ) < rule.edges := by exact_mod_cast (by have := h.edges_gt_one; omega : 0 < rule.edges)
  have hgrowth : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) (h.terminal_degree_spectral_bounds p hp hp').2.1
  obtain ⟨error, herror⟩ := antitone_geometric_log_error
    (rule.limitingRootRadiusTailProbability p)
    (rule.limitingRootRadiusTailProbability_antitone h.edges_gt_one h.vertices_gt_two hp.le hp'.le)
    (rule.network.fullGraph.dist rule.network.source rule.network.target) bound
    (by have := h.scale; omega)
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / (rule.edges : ℝ))
    lower upper (div_pos hgrowth hm) hlower hupper hlowerBound hupperBound
  refine ⟨Real.exp (-error), Real.exp error, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [herror, eventually_gt_atTop 0] with radius herror hradius
  have hpower := rpow_bounds_of_log_error _ (radius : ℝ) _ error herror.1 (by exact_mod_cast hradius) herror.2
  have hexponent : Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        (rule.edges : ℝ)) / Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) =
      -(Real.log (rule.edges : ℝ) - Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
    rw [Real.log_div hgrowth.ne' hm.ne']
    ring
  rwa [hexponent] at hpower

end
end Universality.Rule
