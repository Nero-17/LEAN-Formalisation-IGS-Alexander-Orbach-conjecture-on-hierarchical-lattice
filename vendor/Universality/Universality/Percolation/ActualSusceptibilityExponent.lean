import Universality.Percolation.ActualMomentLogRate
import Universality.Percolation.SubcriticalMomentThreshold

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
attribute [local irreducible] limitingRootSizeMoment

/-- The susceptibility exponent in the paper's signed logarithmic convention. -/
theorem Classical.supercritical_susceptibility_exponent {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    Tendsto (fun p : ℝ => -(Real.log (rule.limitingRootSizeMoment p 1).toReal /
      Real.log |p - critical|)) (𝓝[>] critical)
      (𝓝 (max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 /
          rule.edges)) 0 / Real.log (deriv rule.network.reliability critical))) := by
  have hh := (h.supercritical_root_moment_log_rate critical hc hc' hfixed 1).2.neg
  simpa only [neg_div, neg_neg] using hh

theorem Classical.subcritical_susceptibility_exponent {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ 2 < rule.edges) :
    Tendsto (fun p : ℝ => -(Real.log (rule.limitingRootSizeMoment p 1).toReal /
      Real.log |p - critical|)) (𝓝[<] critical)
      (𝓝 (max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ 2 /
          rule.edges)) 0 / Real.log (deriv rule.network.reliability critical))) := by
  have hh := (h.subcritical_root_moment_log_rate critical hc hc' hfixed 1 hthreshold).2.neg
  simpa only [neg_div, neg_neg] using hh

/-- If the second terminal-degree power reaches the volume factor, the
original subcritical susceptibility is infinite at every positive parameter. -/
theorem Classical.subcritical_susceptibility_eq_top {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical)
    (hthreshold : (rule.edges : ℝ) ≤ (rule.network.fullGraph.degree rule.network.source : ℝ) ^ 2) :
    rule.limitingRootSizeMoment p 1 = ⊤ := by
  exact h.subcritical_root_moment_eq_top critical p hc hc' hfixed hp hpc 1 hthreshold

end
end Universality.Rule
