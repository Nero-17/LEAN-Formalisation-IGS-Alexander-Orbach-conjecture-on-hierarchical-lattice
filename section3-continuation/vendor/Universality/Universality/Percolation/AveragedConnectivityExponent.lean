import Universality.Percolation.CriticalWindowConnectivity
import Universality.Matrix.ColumnGrowth

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The averaged-connectivity logarithmic exponent exists in every fixed
macroscopic distance window and is independent of its endpoints. -/
theorem Classical.averaged_connectivity_logarithmic_exponent {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ => Real.log ((rule.generation n).network.averagedWindowConnectivity p
      (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))
      (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))) /
      ((n : ℝ) * Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)))
      atTop (𝓝 (2 * (Real.log (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal -
        Real.log rule.edges) / Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    h.critical_window_connectivity_bounds p hp hp' hfixed a b ha hab hb
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hedges : 0 < (rule.edges : ℝ) := by
    exact_mod_cast (show 0 < rule.edges from Nat.zero_lt_of_lt h.edges_gt_one)
  have hnormalized := logarithmic_growth_of_eventual_bounds
    (fun n : ℕ => (rule.generation n).network.averagedWindowConnectivity p
      (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))
      (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1)))
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal / (rule.edges : ℝ)) ^ 2)
    lower upper (pow_pos (div_pos hradius hedges) _) hlower hupper (by
      simpa only [← pow_mul] using hbounds)
  have hresult := hnormalized.div_const
    (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))
  simpa only [div_div, Real.log_pow, Real.log_div hradius.ne' hedges.ne', Nat.cast_ofNat] using hresult

/-- The conventional averaged-connectivity exponent is
2 plus the ambient dimension minus twice the critical mass dimension. -/
theorem Classical.averaged_connectivity_exponent {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    Tendsto (fun n : ℕ => 2 - Real.log rule.edges /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) -
      Real.log ((rule.generation n).network.averagedWindowConnectivity p
        (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))
        (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))) /
      ((n : ℝ) * Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)))
      atTop (𝓝 (2 + Real.log rule.edges /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) -
        2 * Real.log (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))) := by
  have hlimit := (tendsto_const_nhds (x := 2 - Real.log rule.edges /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target))).sub
    (h.averaged_connectivity_logarithmic_exponent p hp hp' hfixed a b ha hab hb)
  have heq : 2 - Real.log rule.edges /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) -
      2 * (Real.log (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal -
        Real.log rule.edges) / Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) =
      2 + Real.log rule.edges /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) -
        2 * Real.log (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) := by ring
  simpa only [heq] using hlimit

end
end Universality.Rule
