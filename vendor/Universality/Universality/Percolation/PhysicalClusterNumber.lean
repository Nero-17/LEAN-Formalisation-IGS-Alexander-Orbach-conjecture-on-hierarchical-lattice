import Universality.Percolation.ClusterNumberSizeSum
import Universality.Percolation.PhysicalObservables
import Universality.Percolation.ClusterNumberSmoothness

namespace Universality.Rule
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable (rule : Rule) [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]

/-- The manuscript's cluster-number observable: the annealed probability of
each finite root-cluster size divided by that size, then summed over sizes.
The zero-size summand is zero. Infinite clusters contribute zero. -/
def physicalClusterNumberDensity (hedges : 1 < rule.edges) (p : ℝ) : ℝ :=
  ∑' size : ℕ, rule.physicalFiniteClusterProbability hedges p size / (size : ℝ)

theorem physicalClusterNumberDensity_hasSum (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) (p : Set.Icc (0 : ℝ) 1) :
    HasSum (fun size => rule.physicalFiniteClusterProbability hedges p size / (size : ℝ))
      (rule.network.clusterNumberSeries p) := by
  simpa only [rule.physicalFiniteClusterProbability_eq hedges hvertices p.property.1 p.property.2]
    using rule.clusterNumberSeries_hasSum_root_size_quotients hedges hvertices p

theorem physicalClusterNumberDensity_eq (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) (p : Set.Icc (0 : ℝ) 1) :
    rule.physicalClusterNumberDensity hedges p = rule.network.clusterNumberSeries p :=
  (rule.physicalClusterNumberDensity_hasSum hedges hvertices p).tsum_eq

theorem physicalClusterNumberDensity_eventually_eq (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    rule.physicalClusterNumberDensity hedges =ᶠ[𝓝 p] rule.network.clusterNumberAnalyticExtension := by
  filter_upwards [Ioo_mem_nhds hp hp'] with q hq
  rw [rule.network.clusterNumberAnalyticExtension_eq ⟨q, hq.1.le, hq.2.le⟩]
  exact rule.physicalClusterNumberDensity_eq hedges hvertices ⟨q, hq.1.le, hq.2.le⟩

variable {rule}

theorem Classical.physical_cluster_number_contDiffAt (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ)
    (hthreshold : deriv rule.network.reliability critical ^ order < (rule.edges : ℝ)) :
    ContDiffAt ℝ order (rule.physicalClusterNumberDensity h.edges_gt_one) critical :=
  (h.cluster_number_contDiffAt critical hc hc' hfixed order hthreshold).congr_of_eventuallyEq
    (rule.physicalClusterNumberDensity_eventually_eq h.edges_gt_one h.vertices_gt_two critical hc hc')

/-- The raw-alpha response is stated for the actual annealed cluster-number
observable, with its derivatives rather than derivatives of a formal series. -/
theorem Classical.physical_cluster_number_raw_alpha_criterion (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (order : ℕ) (horder : 3 ≤ order)
    (hthreshold : deriv rule.network.reliability critical ^ order < (rule.edges : ℝ))
    (hvanish : ∀ i, 3 ≤ i → i < order →
      iteratedDeriv i (rule.physicalClusterNumberDensity h.edges_gt_one) critical = 0)
    (hleading : iteratedDeriv order (rule.physicalClusterNumberDensity h.edges_gt_one) critical ≠ 0) :
    ((∀ᶠ p in 𝓝[<] critical, iteratedDeriv 3 (rule.physicalClusterNumberDensity h.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 (rule.physicalClusterNumberDensity h.edges_gt_one) p| /
        Real.log |p - critical|) (𝓝[<] critical) (𝓝 (2 - (order : ℝ)))) ∧
    ((∀ᶠ p in 𝓝[>] critical, iteratedDeriv 3 (rule.physicalClusterNumberDensity h.edges_gt_one) p ≠ 0) ∧
      Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 (rule.physicalClusterNumberDensity h.edges_gt_one) p| /
        Real.log |p - critical|) (𝓝[>] critical) (𝓝 (2 - (order : ℝ)))) :=
  raw_cluster_number_alpha_criterion _ critical order horder
    (h.physical_cluster_number_contDiffAt critical hc hc' hfixed order hthreshold) hvanish hleading

end
end Universality.Rule
