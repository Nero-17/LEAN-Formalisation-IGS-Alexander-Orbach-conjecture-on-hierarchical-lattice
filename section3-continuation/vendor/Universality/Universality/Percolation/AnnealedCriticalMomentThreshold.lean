import Universality.Percolation.AnnealedCriticalMomentFinite
import Universality.Percolation.AnnealedCriticalMomentDivergence

namespace Universality.Rule
noncomputable section
open scoped ENNReal

/-- Exact critical moment threshold, including divergence at equality, for
the actual limiting uniform-root cluster-size law. -/
theorem Classical.critical_root_moment_finite_iff {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) :
    rule.limitingRootSizeMoment p order ≠ ⊤ ↔
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order + 1) <
        (rule.edges : ℝ) := by
  constructor
  · intro hfinite
    by_contra hthreshold
    exact hfinite (h.critical_root_moment_eq_top p hp hp' hfixed order (le_of_not_gt hthreshold))
  · exact h.critical_root_moment_ne_top p hp hp' hfixed order

end
end Universality.Rule
