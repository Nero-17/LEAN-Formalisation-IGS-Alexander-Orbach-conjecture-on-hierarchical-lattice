import Universality.Percolation.ClusterNumberSmoothness

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology

theorem Classical.cluster_number_contDiffAt_on_unit {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : deriv rule.network.reliability critical ^ order < (rule.edges : ℝ))
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ order rule.network.clusterNumberAnalyticExtension p := by
  by_cases hpoint : p = critical
  · subst p
    exact h.cluster_number_contDiffAt critical hc hc' hfixed order hthreshold
  exact (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.1 hp.2 hpoint).contDiffAt

theorem Classical.cluster_number_iteratedDeriv_continuousOn_unit {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : deriv rule.network.reliability critical ^ order < (rule.edges : ℝ)) :
    ContinuousOn (iteratedDeriv order rule.network.clusterNumberAnalyticExtension) (Icc (0 : ℝ) 1) := by
  intro p hp
  have hregular := h.cluster_number_contDiffAt_on_unit critical hc hc' hfixed order hthreshold p hp
  have hderivative := contDiffAt_iteratedDeriv_of_add rule.network.clusterNumberAnalyticExtension p 0 order
    (by simpa only [zero_add] using hregular)
  exact hderivative.continuousAt.continuousWithinAt

end
end Universality.Rule

namespace Universality.FiniteNetwork
noncomputable section
open Filter Set Polynomial
open scoped Topology

theorem clusterNumberAnalyticExtension_equation {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (hedges : 1 < edges) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    (edges : ℝ) * R.clusterNumberAnalyticExtension p -
      R.clusterNumberAnalyticExtension (R.reliability p) =
        ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) * R.expectedInternalClusterNumber p := by
  have hnext := R.clusterNumberAnalyticExtension_eq (R.unitReliability ⟨p, hp⟩)
  change R.clusterNumberAnalyticExtension (R.reliability p) = _ at hnext
  rw [R.clusterNumberAnalyticExtension_eq ⟨p, hp⟩, hnext]
  exact R.clusterNumberSeries_equation hedges ⟨p, hp⟩

theorem clusterNumberAnalyticExtension_equation_eventually {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (hedges : 1 < edges) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (fun q => (edges : ℝ) * R.clusterNumberAnalyticExtension q -
      R.clusterNumberAnalyticExtension (R.reliability q)) =ᶠ[𝓝 p]
        (fun q => ((edges : ℝ) - 1) / ((vertices : ℝ) - 2) *
          (R.internalClusterPolynomial.map (Int.castRingHom ℝ)).eval q) := by
  filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
  rw [Polynomial.eval_map, internalClusterPolynomial_eval]
  exact R.clusterNumberAnalyticExtension_equation hedges q ⟨hq.1.le, hq.2.le⟩

end
end Universality.FiniteNetwork
