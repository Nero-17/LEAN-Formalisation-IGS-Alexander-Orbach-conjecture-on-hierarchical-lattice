import Universality.Percolation.PhysicalClusterNumber
namespace Universality.Rule
noncomputable section
open Set Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable {rule : Rule} [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]

theorem physicalClusterNumberDensity_eqOn (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) :
    EqOn (rule.physicalClusterNumberDensity hedges) rule.network.clusterNumberAnalyticExtension
      (Icc (0 : ℝ) 1) := by
  intro p hp
  rw [rule.network.clusterNumberAnalyticExtension_eq ⟨p, hp⟩]
  exact rule.physicalClusterNumberDensity_eq hedges hvertices ⟨p, hp⟩

/-- At an interior offcritical parameter the physical observable itself is
analytic on a real neighborhood. -/
theorem Classical.physical_cluster_number_analyticAt_offcritical (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 < p) (hp' : p < 1) (hne : p ≠ critical) :
    AnalyticAt ℝ (rule.physicalClusterNumberDensity h.edges_gt_one) p :=
  (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.le hp'.le hne).congr
    (rule.physicalClusterNumberDensity_eventually_eq h.edges_gt_one h.vertices_gt_two p hp hp').symm

/-- This endpoint-inclusive statement is within [0,1]; the physical observable
was defined to vanish outside the probability interval. -/
theorem Classical.physical_cluster_number_analyticWithinAt_offcritical (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hne : p ≠ critical) :
    AnalyticWithinAt ℝ (rule.physicalClusterNumberDensity h.edges_gt_one) (Icc (0 : ℝ) 1) p :=
  (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp hp' hne).analyticWithinAt.congr
    (physicalClusterNumberDensity_eqOn h.edges_gt_one h.vertices_gt_two)
    (physicalClusterNumberDensity_eqOn h.edges_gt_one h.vertices_gt_two ⟨hp, hp'⟩)

theorem Classical.physical_cluster_number_has_analytic_extension (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hne : p ≠ critical) :
    ∃ extension : ℝ → ℝ, AnalyticAt ℝ extension p ∧
      EqOn (rule.physicalClusterNumberDensity h.edges_gt_one) extension (Icc (0 : ℝ) 1) :=
  ⟨rule.network.clusterNumberAnalyticExtension,
    h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp hp' hne,
    physicalClusterNumberDensity_eqOn h.edges_gt_one h.vertices_gt_two⟩

end
end Universality.Rule
