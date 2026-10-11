import Universality.Graph.UniformRootSizeIdentification
import Universality.Percolation.RootedLimitSizeLaw

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- At the nontrivial critical fixed point, the actual sampled root component
is finite almost surely. This is deduced from the proved physical size law. -/
theorem Classical.ae_uniformRoot_critical_cluster_finite {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (hfixed : rule.network.reliability (p : ℝ) = p) :
    ∀ᵐ sample ∂rule.uniformRootSampleLaw h.edges_gt_one p,
      Set.Finite {vertex |
        ((rule.ancestralTower sample.1 sample.2.2.1).openGraph
          ((rule.ancestralTower sample.1 sample.2.2.1).sampledConfiguration sample.2.2.2)).Reachable
            ((rule.ancestralTower sample.1 sample.2.2.1).vertex 0 sample.2.1) vertex} := by
  classical
  have hzero : (rule.uniformRootSampleLaw h.edges_gt_one p).real
      {sample | rule.uniformRootInfiniteClusterEvent sample} = 0 := by
    rw [rule.uniformRootInfiniteClusterProbability_eq_escapingRootMass
      h.edges_gt_one h.vertices_gt_two p, h.critical_escapingRootMass_zero p hp hp' hfixed]
  have hnull := (measureReal_eq_zero_iff).mp hzero
  have hevent : ∀ᵐ sample ∂rule.uniformRootSampleLaw h.edges_gt_one p,
      ¬ rule.uniformRootInfiniteClusterEvent sample := by
    apply ae_iff.mpr
    simpa only [not_not] using hnull
  filter_upwards [hevent] with sample hsample
  by_contra hinfinite
  exact hsample ((rule.uniformRootInfiniteClusterEvent_iff sample).mpr hinfinite)

end
end Universality.Rule
