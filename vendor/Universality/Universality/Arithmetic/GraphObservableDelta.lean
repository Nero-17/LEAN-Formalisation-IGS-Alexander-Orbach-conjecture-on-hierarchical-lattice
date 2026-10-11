import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Percolation.CriticalRootSizePowerBounds

/-!
The delta exponent is identified through the actual limiting finite-volume
uniform-vertex cluster-size probabilities. A number supplied externally is
identified by its logarithmic limit; it is not defined to be a dimension ratio.
Identification of the thermodynamic size law with a law on an infinite rooted
graph remains a separate assertion and is not assumed here.
-/

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- The size law used below is the limit of actual finite-generation
Bernoulli percolation probabilities observed at an independent uniform vertex. -/
theorem Classical.limiting_root_size_probability_is_volume_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (size : ℕ) :
    Tendsto (fun depth : ℕ =>
      (rule.generation depth).network.uniformVertexClusterMassProbability p size)
      atTop (𝓝 (rule.limitingRootSizeProbability p size)) :=
  rule.generation_uniformVertexClusterMassProbability_tendsto
    h.edges_gt_one h.vertices_gt_two hp.le hp'.le size
theorem Classical.critical_delta_dimension_value {rule : Rule} (h : rule.Classical)
    (p : ℝ) :
    rule.criticalDimensions p 1 / (rule.criticalDimensions p 0 - rule.criticalDimensions p 1) =
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        (Real.log (rule.edges : ℝ) -
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)) := by
  have hscale : Real.log
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast h.scale))
  change ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) /
    (Real.log (rule.edges : ℝ) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) -
     Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ))) = _
  rw [← sub_div, div_div_div_cancel_right₀ hscale]

/-- The value established by the actual size law is positive. -/
theorem Classical.critical_delta_criticalDimensions_pos {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    0 < rule.criticalDimensions p 1 /
      (rule.criticalDimensions p 0 - rule.criticalDimensions p 1) := by
  rw [h.critical_delta_dimension_value]
  exact (h.critical_delta_value p hp hp' hfixed).1

/-- The actual point-probability slope in the paper's inverse-delta convention. -/
theorem Classical.critical_inverse_delta_criticalDimensions {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    Tendsto (fun size : ℕ =>
      -1 - Real.log (rule.limitingRootSizeProbability p size) / Real.log (size : ℝ))
      atTop (𝓝 (1 / (rule.criticalDimensions p 1 /
        (rule.criticalDimensions p 0 - rule.criticalDimensions p 1)))) := by
  rw [h.critical_delta_dimension_value]
  exact (h.critical_delta_value p hp hp' hfixed).2

/-- Every externally supplied delta satisfying the actual logarithmic limit
has the proved dimension value. No nonzero or positivity premise on delta is
needed: inversion is injective on the whole real field. -/
theorem Classical.critical_delta_eq_criticalDimensions {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (delta : ℝ)
    (hlimit : Tendsto (fun size : ℕ =>
      -1 - Real.log (rule.limitingRootSizeProbability p size) / Real.log (size : ℝ))
      atTop (𝓝 (1 / delta))) :
    delta = rule.criticalDimensions p 1 /
      (rule.criticalDimensions p 0 - rule.criticalDimensions p 1) := by
  have hinverse := tendsto_nhds_unique hlimit
    (h.critical_inverse_delta_criticalDimensions p hp hp' hfixed)
  exact inv_injective (by simpa only [one_div] using hinverse)

end
end Universality.Rule

#print axioms Universality.Rule.Classical.limiting_root_size_probability_is_volume_limit
#print axioms Universality.Rule.Classical.critical_delta_criticalDimensions_pos
#print axioms Universality.Rule.Classical.critical_inverse_delta_criticalDimensions
#print axioms Universality.Rule.Classical.critical_delta_eq_criticalDimensions

