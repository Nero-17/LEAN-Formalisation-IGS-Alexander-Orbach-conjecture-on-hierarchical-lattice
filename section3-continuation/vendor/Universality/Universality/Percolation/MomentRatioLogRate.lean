import Universality.Percolation.ActualMomentLogRate
import Universality.Percolation.MassSpectralLowerBound

namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem logarithmic_ratio_from_log_rates {α : Type*} (filter : Filter α)
    (first second denominator : α → ℝ) (firstRate secondRate : ℝ)
    (hfirst : Tendsto (fun x => Real.log (first x) / denominator x) filter (𝓝 firstRate))
    (hsecond : Tendsto (fun x => Real.log (second x) / denominator x) filter (𝓝 secondRate))
    (hfirstPos : ∀ᶠ x in filter, 0 < first x) (hsecondPos : ∀ᶠ x in filter, 0 < second x) :
    Tendsto (fun x => -(Real.log (second x / first x) / denominator x)) filter
      (𝓝 (firstRate - secondRate)) := by
  apply (hfirst.sub hsecond).congr'
  filter_upwards [hfirstPos, hsecondPos] with x hf hs
  rw [Real.log_div hs.ne' hf.ne', sub_div]
  ring

namespace Rule
attribute [local irreducible] limitingRootSizeMoment

theorem Classical.supercritical_root_moment_ratio_log_rate {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) :
    Tendsto (fun p : ℝ => -(Real.log
      ((rule.limitingRootSizeMoment p (order + 1)).toReal / (rule.limitingRootSizeMoment p order).toReal) /
        Real.log |p - critical|)) (𝓝[>] critical)
      (𝓝 ((max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 2) / rule.edges)) 0 -
        max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0) /
          Real.log (deriv rule.network.reliability critical))) := by
  have hfirst := h.supercritical_root_moment_log_rate critical hc hc' hfixed order
  have hsecond := h.supercritical_root_moment_log_rate critical hc hc' hfixed (order + 1)
  have hh := logarithmic_ratio_from_log_rates (𝓝[>] critical)
    (fun p => (rule.limitingRootSizeMoment p order).toReal)
    (fun p => (rule.limitingRootSizeMoment p (order + 1)).toReal)
    (fun p => Real.log |p - critical|) _ _ hfirst.2 hsecond.2 hfirst.1 hsecond.1
  have hvalue (first second denominator : ℝ) :
      -first / denominator - -second / denominator = (second - first) / denominator := by ring
  simpa only [hvalue] using hh

theorem Classical.subcritical_root_moment_ratio_log_rate {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 2) < rule.edges) :
    Tendsto (fun p : ℝ => -(Real.log
      ((rule.limitingRootSizeMoment p (order + 1)).toReal / (rule.limitingRootSizeMoment p order).toReal) /
        Real.log |p - critical|)) (𝓝[<] critical)
      (𝓝 ((max (Real.log
        (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 2) / rule.edges)) 0 -
        max (Real.log (((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order + 1) / rule.edges)) 0) /
          Real.log (deriv rule.network.reliability critical))) := by
  have hdegree : (1 : ℝ) ≤ rule.network.fullGraph.degree rule.network.source := by
    have hh := (h.terminal_degree_spectral_bounds critical hc hc').1
    exact_mod_cast (show 1 ≤ rule.network.fullGraph.degree rule.network.source by omega)
  have hthresholdLower : (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order + 1) < rule.edges :=
    (pow_le_pow_right₀ hdegree (by omega : order + 1 ≤ order + 2)).trans_lt hthreshold
  have hfirst := h.subcritical_root_moment_log_rate critical hc hc' hfixed order hthresholdLower
  have hsecond := h.subcritical_root_moment_log_rate critical hc hc' hfixed (order + 1) hthreshold
  have hh := logarithmic_ratio_from_log_rates (𝓝[<] critical)
    (fun p => (rule.limitingRootSizeMoment p order).toReal)
    (fun p => (rule.limitingRootSizeMoment p (order + 1)).toReal)
    (fun p => Real.log |p - critical|) _ _ hfirst.2 hsecond.2 hfirst.1 hsecond.1
  have hvalue (first second denominator : ℝ) :
      -first / denominator - -second / denominator = (second - first) / denominator := by ring
  simpa only [hvalue] using hh

end Rule
end
end Universality
