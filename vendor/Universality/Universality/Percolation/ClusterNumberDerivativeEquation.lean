import Universality.Analysis.CompactRenormalizationResponse
import Universality.Percolation.ClusterNumberAnalyticity

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology

 theorem Classical.cluster_number_analyticExtension_hasDerivAt_critical {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    HasDerivAt rule.network.clusterNumberAnalyticExtension
      ((((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
          (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).derivative.eval critical) /
        ((rule.edges : ℝ) - deriv rule.network.reliability critical)) critical := by
  apply (h.cluster_number_hasDerivAt_critical critical hc hc' hfixed).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hc hc'] with p hp
  rw [rule.network.clusterNumberAnalyticExtension_eq ⟨p, hp.1.le, hp.2.le⟩,
    rule.network.clusterNumberDensityExtension_eq ⟨p, hp.1.le, hp.2.le⟩]

theorem Classical.cluster_number_differentiableAt {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    DifferentiableAt ℝ rule.network.clusterNumberAnalyticExtension p := by
  by_cases heq : p = critical
  · subst p
    exact (h.cluster_number_analyticExtension_hasDerivAt_critical critical hc hc' hfixed).differentiableAt
  exact (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp hp' heq).differentiableAt

theorem Classical.cluster_number_deriv_equation {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hp' : p < 1) :
    (rule.edges : ℝ) * deriv rule.network.clusterNumberAnalyticExtension p -
      deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability p) *
        deriv rule.network.reliability p =
      ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
        (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).derivative.eval p := by
  let hclosed := rule.network.unitReliability ⟨p, hp.le, hp'.le⟩
  have hlower : 0 ≤ rule.network.reliability p := hclosed.property.1
  have hupper : rule.network.reliability p ≤ 1 := hclosed.property.2
  have hleft := ((h.cluster_number_differentiableAt critical p hc hc' hfixed hp.le hp'.le).hasDerivAt.const_mul
    (rule.edges : ℝ)).sub
      (((h.cluster_number_differentiableAt critical (rule.network.reliability p) hc hc' hfixed
        hlower hupper).hasDerivAt).comp p
          (rule.network.hasDerivAt_reliability p))
  have hright := ((rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).hasDerivAt p).const_mul
    (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2))
  have heq : (fun q => ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
      (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).eval q) =ᶠ[𝓝 p]
      (fun q => (rule.edges : ℝ) * rule.network.clusterNumberAnalyticExtension q -
        rule.network.clusterNumberAnalyticExtension (rule.network.reliability q)) := by
    filter_upwards [Ioo_mem_nhds hp hp'] with q hq
    have heq := rule.network.clusterNumberSeries_equation h.edges_gt_one ⟨q, hq.1.le, hq.2.le⟩
    have hnext := rule.network.clusterNumberAnalyticExtension_eq
      (rule.network.unitReliability ⟨q, hq.1.le, hq.2.le⟩)
    change rule.network.clusterNumberAnalyticExtension (rule.network.reliability q) = _ at hnext
    rw [rule.network.clusterNumberAnalyticExtension_eq ⟨q, hq.1.le, hq.2.le⟩, hnext]
    simpa only [Polynomial.eval_map, internalClusterPolynomial_eval] using heq.symm
  simpa only [(rule.network.hasDerivAt_reliability p).deriv] using (hleft.congr_of_eventuallyEq heq).unique hright

theorem Classical.unitReliability_escape {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ p : Icc (0 : ℝ) 1,
      p ≠ ⟨critical, hc.le, hc'.le⟩ → ∃ n : ℕ,
        radius ≤ dist (rule.network.unitReliability^[n] p) ⟨critical, hc.le, hc'.le⟩ := by
  obtain ⟨radius, hradius, hradiusUpper⟩ := exists_between (lt_min hc (sub_pos.mpr hc'))
  refine ⟨radius, hradius, ?_⟩
  intro p hne
  have hneVal : p.val ≠ critical := fun heq => hne (Subtype.ext heq)
  rcases lt_or_gt_of_ne hneVal with hp | hp
  · have hlimit := (rule.network.iterate_reliability_tendsto_zero critical p.val hc hc' hfixed
      p.property.1 hp h.scale).sub_const critical |>.abs
    have hrad : radius < |(0 : ℝ) - critical| := by
      simpa [abs_of_pos hc] using hradiusUpper.trans_le (min_le_left _ _)
    obtain ⟨n, hn⟩ := (hlimit.eventually (lt_mem_nhds hrad)).exists
    exact ⟨n, by simpa only [Subtype.dist_eq, Real.dist_eq,
      rule.network.unitReliability_iterate_val] using hn.le⟩
  · have hlimit := (rule.network.iterate_reliability_tendsto_one critical p.val hc hc' hfixed
      hp p.property.2 h.scale).sub_const critical |>.abs
    have hrad : radius < |(1 : ℝ) - critical| := by
      rw [abs_of_pos (sub_pos.mpr hc')]
      exact hradiusUpper.trans_le (min_le_right _ _)
    obtain ⟨n, hn⟩ := (hlimit.eventually (lt_mem_nhds hrad)).exists
    exact ⟨n, by simpa only [Subtype.dist_eq, Real.dist_eq,
      rule.network.unitReliability_iterate_val] using hn.le⟩

end
end Universality.Rule


