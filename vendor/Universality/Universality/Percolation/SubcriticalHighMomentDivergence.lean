import Universality.Percolation.SubcriticalMomentThreshold
import Universality.Percolation.MassSpectralLowerBound
import Universality.Percolation.ClassicalClusterNumber

namespace Universality.Rule
noncomputable section
open scoped ENNReal

/-- At every strictly positive subcritical parameter, sufficiently high
finite-cluster root moments are infinite. In particular the original moment
ratios cannot all be finite on the subcritical side. -/
theorem Classical.subcritical_eventually_root_moment_eq_top {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    ∀ᶠ order : ℕ in Filter.atTop, rule.limitingRootSizeMoment p order = ⊤ := by
  have hdegree : (1 : ℝ) < rule.network.fullGraph.degree rule.network.source := by
    have hh := (h.terminal_degree_spectral_bounds critical hc hc').1
    exact_mod_cast (show 1 < rule.network.fullGraph.degree rule.network.source by omega)
  have hm : (1 : ℝ) ≤ rule.edges := by exact_mod_cast h.edges_gt_one.le
  obtain ⟨start, _, hstart⟩ := exists_nat_pow_near hm hdegree
  filter_upwards [Filter.eventually_ge_atTop start] with order horder
  apply h.subcritical_root_moment_eq_top critical p hc hc' hfixed hp hpc order
  exact hstart.le.trans (pow_le_pow_right₀ hdegree.le (by omega : start + 1 ≤ order + 1))

end
end Universality.Rule
