import Universality.Percolation.PhysicalCriticalExponents
import Universality.Percolation.AveragedConnectivityExponent
import Universality.Percolation.CrossingExponent
import Universality.Algebra.ExponentRecovery

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

def HasCriticalExponents (rule : Rule) [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (critical beta nu delta eta : ℝ) : Prop :=
  Tendsto (fun p : ℝ => Real.log (rule.physicalInfiniteClusterProbability hedges p) / Real.log (p - critical))
    (𝓝[>] critical) (𝓝 beta) ∧
  Tendsto (fun p : ℝ => -Real.log (rule.network.crossingCorrelationLength p) / Real.log (critical - p))
    (𝓝[<] critical) (𝓝 nu) ∧
  0 < delta ∧
  (∀ᶠ size : ℕ in atTop, 0 < rule.physicalFiniteClusterProbability hedges critical size) ∧
  Tendsto (fun size : ℕ => -1 - Real.log (rule.physicalFiniteClusterProbability hedges critical size) /
    Real.log (size : ℝ)) atTop (𝓝 (1 / delta)) ∧
  ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    Tendsto (fun n : ℕ => 2 - Real.log rule.edges /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) -
      Real.log ((rule.generation n).network.averagedWindowConnectivity critical
        (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))
        (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))) /
      ((n : ℝ) * Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target)))
      atTop (𝓝 eta)

variable {rule : Rule} [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]

theorem Classical.hasCriticalExponents (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    rule.HasCriticalExponents h.edges_gt_one critical
      ((Real.log (rule.edges : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)) /
        Real.log (deriv rule.network.reliability critical))
      (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) /
        Real.log (deriv rule.network.reliability critical))
      (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
        (Real.log (rule.edges : ℝ) -
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal)))
      (2 + Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) -
        2 * Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) := by
  refine ⟨h.physical_beta_exponent critical hc hc' hfixed,
    h.crossing_length_exponent critical hc hc' hfixed,
    (h.critical_delta_value critical hc hc' hfixed).1,
    (h.physical_delta_exponent critical hc hc' hfixed).1, ?_, ?_⟩
  · simpa only [one_div, inv_div] using (h.physical_delta_exponent critical hc hc' hfixed).2
  · exact h.averaged_connectivity_exponent critical hc hc' hfixed

theorem critical_exponents_unique (hedges : 1 < rule.edges)
    (critical betaFirst nuFirst deltaFirst etaFirst betaSecond nuSecond deltaSecond etaSecond : ℝ)
    (hfirst : rule.HasCriticalExponents hedges critical betaFirst nuFirst deltaFirst etaFirst)
    (hsecond : rule.HasCriticalExponents hedges critical betaSecond nuSecond deltaSecond etaSecond) :
    betaFirst = betaSecond ∧ nuFirst = nuSecond ∧ deltaFirst = deltaSecond ∧ etaFirst = etaSecond := by
  have hbeta := tendsto_nhds_unique hfirst.1 hsecond.1
  have hnu := tendsto_nhds_unique hfirst.2.1 hsecond.2.1
  have hdeltaInverse := tendsto_nhds_unique hfirst.2.2.2.2.1 hsecond.2.2.2.2.1
  have hdelta : deltaFirst = deltaSecond := by
    have hh := congrArg (fun x : ℝ => x⁻¹) hdeltaInverse
    simpa only [one_div, inv_inv] using hh
  have heta := tendsto_nhds_unique
    (hfirst.2.2.2.2.2 (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num))
    (hsecond.2.2.2.2.2 (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num))
  exact ⟨hbeta, hnu, hdelta, heta⟩

end
end Universality.Rule
