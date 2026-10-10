import Universality.Percolation.ClusterNumberVolumeLimit
import Universality.Percolation.PivotalResponseBound
import Universality.Graph.ClassicalRule

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.edges_gt_one {rule : Rule} (h : rule.Classical) : 1 < rule.edges := by
  obtain ⟨p, hp, hp', hfixed⟩ := h.exists_interior_fixed_point
  have hderiv := rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale
  have hsquare := rule.network.pivotal_response_sq_lt_edges p hp hp' hfixed h.scale
  have hreal : (1 : ℝ) < rule.edges := by nlinarith
  exact_mod_cast hreal

theorem Classical.vertices_gt_two {rule : Rule} (h : rule.Classical) : 2 < rule.vertices := by
  obtain ⟨walk, hpath⟩ := (h.connected rule.network.target).exists_isPath
  have hlength := hpath.length_lt
  have hdistance := rule.network.fullGraph.dist_le walk
  have hscale := h.scale
  simp only [Fintype.card_fin] at hlength
  omega

/-- The physical cluster-number density exists as a volume limit and is the
unique bounded solution of the manuscript's functional equation. -/
theorem Classical.cluster_number_density {rule : Rule} (h : rule.Classical) :
    (∀ p : Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => (rule.generation n).network.expectedClusterNumber p.val /
        ((rule.generation n).vertices : ℝ)) atTop (𝓝 (rule.network.clusterNumberSeries p))) ∧
    (∃ bound : ℝ, ∀ p, |rule.network.clusterNumberSeries p| ≤ bound) ∧
    (∀ p, (rule.edges : ℝ) * rule.network.clusterNumberSeries p -
      rule.network.clusterNumberSeries (rule.network.unitReliability p) =
      ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
        rule.network.expectedInternalClusterNumber p.val) ∧
    (∀ solution : Set.Icc (0 : ℝ) 1 → ℝ, (∃ bound : ℝ, ∀ p, |solution p| ≤ bound) →
      (∀ p, (rule.edges : ℝ) * solution p - solution (rule.network.unitReliability p) =
        ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
          rule.network.expectedInternalClusterNumber p.val) →
      solution = rule.network.clusterNumberSeries) := by
  refine ⟨rule.generation_cluster_number_density_tendsto h.edges_gt_one h.vertices_gt_two,
    rule.network.clusterNumberSeries_bounded h.edges_gt_one,
    rule.network.clusterNumberSeries_equation h.edges_gt_one, ?_⟩
  intro solution ⟨bound, hbound⟩ hequation
  exact rule.network.clusterNumberSeries_unique h.edges_gt_one solution bound hbound hequation

end
end Universality.Rule
