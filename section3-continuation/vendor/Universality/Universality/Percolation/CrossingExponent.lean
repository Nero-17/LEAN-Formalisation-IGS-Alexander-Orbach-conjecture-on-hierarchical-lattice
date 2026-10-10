import Universality.Percolation.CrossingLengthCriticalBound
import Universality.Analysis.BoundedLogError

namespace Universality.Rule
noncomputable section
open Filter FiniteNetwork
open scoped Topology

/-- The physical crossing-length exponent, with the volume/iteration limit
taken first. The correlation length is identified with that actual limit. -/
theorem Classical.crossing_length_exponent {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto (fun p : ℝ => -Real.log (rule.network.crossingCorrelationLength p) / Real.log (critical - p))
      (𝓝[<] critical)
      (𝓝 (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
        Real.log (deriv rule.network.reliability critical))) := by
  obtain ⟨radius, bound, hradius, _, _, hbound⟩ :=
    h.crossing_length_log_error_bound critical hc hc' hfixed
  have hnear : ∀ᶠ p in 𝓝[<] critical, critical - radius < p :=
    (lt_mem_nhds (show critical - radius < critical by linarith)).filter_mono nhdsWithin_le_nhds
  have herror : ∀ᶠ p in 𝓝[<] critical,
      |Real.log (rule.network.inverseCrossingLength p) -
        (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) /
          Real.log (deriv rule.network.reliability critical)) * Real.log (critical - p)| ≤ bound := by
    filter_upwards [hnear, self_mem_nhdsWithin] with p hp hpc
    exact hbound p hp hpc
  have hlimit := tendsto_ratio_of_bounded_error (𝓝[<] critical)
    (fun p => Real.log (rule.network.inverseCrossingLength p)) (fun p => Real.log (critical - p))
    _ bound (tendsto_log_left_deviation critical) herror
  simpa only [crossingCorrelationLength, one_div, Real.log_inv, neg_neg] using hlimit

end
end Universality.Rule
