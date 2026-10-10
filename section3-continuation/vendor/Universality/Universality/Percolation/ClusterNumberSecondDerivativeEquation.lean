import Universality.Percolation.ClusterNumberFirstContinuity

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology

theorem Classical.reliability_ne_critical {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hne : p ≠ critical) :
    rule.network.reliability p ≠ critical := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ne_of_lt ((rule.network.reliability_le_parameter_below_fixed critical p hc hc'
      hfixed hp hlt h.scale).trans_lt hlt)
  · exact ne_of_gt (hgt.trans_le (rule.network.parameter_le_reliability_above_fixed critical p hc hc'
      hfixed hgt hp' h.scale))

theorem Classical.cluster_number_second_deriv_equation {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) :
    (rule.edges : ℝ) * deriv (deriv rule.network.clusterNumberAnalyticExtension) p =
      (rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)).derivative.eval p ^ 2 *
          deriv (deriv rule.network.clusterNumberAnalyticExtension) (rule.network.reliability p) +
        (rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)).derivative.derivative.eval p *
          deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability p) +
        ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
          (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).derivative.derivative.eval p := by
  let crossing := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  let forcing := rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)
  have hcrossing (q : ℝ) : crossing.derivative.eval q = deriv rule.network.reliability q := by
    dsimp [crossing]
    rw [Polynomial.derivative_map, Polynomial.eval_map, (rule.network.hasDerivAt_reliability q).deriv]
  let hclosed := rule.network.unitReliability ⟨p, hp.le, hp'.le⟩
  have hnext := h.cluster_number_analyticAt_offcritical critical (rule.network.reliability p) hc hc' hfixed
    hclosed.property.1 hclosed.property.2 (h.reliability_ne_critical critical p hc hc' hfixed hp.le hp'.le hne)
  have hcurrent := h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.le hp'.le hne
  have hiteration : HasDerivAt rule.network.reliability (crossing.derivative.eval p) p := by
    rw [hcrossing]
    exact (rule.network.hasDerivAt_reliability p).differentiableAt.hasDerivAt
  have hleft := (hcurrent.deriv.differentiableAt.hasDerivAt.const_mul (rule.edges : ℝ)).sub
    (((hnext.deriv.differentiableAt.hasDerivAt.comp p hiteration).mul
      (crossing.derivative.hasDerivAt p)))
  have hright := (forcing.derivative.hasDerivAt p).const_mul
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2))
  have heq : (fun q => ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
      forcing.derivative.eval q) =ᶠ[𝓝 p]
      (fun q => (rule.edges : ℝ) * deriv rule.network.clusterNumberAnalyticExtension q -
        deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability q) *
          crossing.derivative.eval q) := by
    filter_upwards [Ioo_mem_nhds hp hp'] with q hq
    rw [hcrossing]
    exact (h.cluster_number_deriv_equation critical q hc hc' hfixed hq.1 hq.2).symm
  have hresult := (hleft.congr_of_eventuallyEq heq).unique hright
  dsimp [crossing, forcing] at hresult
  nlinarith

end
end Universality.Rule




