import Universality.Percolation.SubcriticalMomentFinite
import Universality.Percolation.SubcriticalMomentDivergence

namespace Universality.Rule
noncomputable section
open scoped ENNReal

/-- Exact positive-subcritical moment threshold for the actual limiting
uniform-root cluster-size distribution. The endpoint p = 0 is excluded. -/
theorem Classical.subcritical_root_moment_finite_iff {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical)
    (order : ℕ) :
    rule.limitingRootSizeMoment p order ≠ ⊤ ↔
      (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) < (rule.edges : ℝ) := by
  constructor
  · intro hfinite
    by_contra hthreshold
    exact hfinite (h.subcritical_root_moment_eq_top critical p hc hc' hfixed hp hpc order
      (le_of_not_gt hthreshold))
  · exact h.subcritical_root_moment_ne_top critical p hc hc' hfixed hp.le hpc order

end
end Universality.Rule
