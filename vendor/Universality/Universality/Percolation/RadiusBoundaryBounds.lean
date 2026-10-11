import Universality.Percolation.BirthRadiusRecursion
import Universality.Percolation.InternalClusterMassLimit

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem radiusRootCount_boundary_bounds (configuration : Configuration edges) (radius : ℕ) :
    (R.internalRadiusRootCount configuration radius : ℝ) ≤
      (∑ root : Fin vertices, if radius ≤ R.rootClusterRadius configuration root then (1 : ℝ) else 0) ∧
    (∑ root : Fin vertices, if radius ≤ R.rootClusterRadius configuration root then (1 : ℝ) else 0) ≤
      R.internalRadiusRootCount configuration radius + R.internalSelectedMass true true configuration + 2 := by
  have hroot := congrArg (fun count : ℕ => (count : ℝ)) (R.root_radius_tail_count configuration radius)
  push_cast at hroot
  rw [hroot]
  have hinternal : (R.internalRadiusRootCount configuration radius : ℝ) =
      ∑ cluster ∈ R.clusterFamily configuration,
        if R.source ∉ cluster ∧ R.target ∉ cluster then (R.clusterRadiusRootCount cluster radius : ℝ) else 0 := by
    simp only [internalRadiusRootCount, internalClusterFamily, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_zero]
  have hmass : (R.internalClusterMass configuration : ℝ) =
      ∑ cluster ∈ R.clusterFamily configuration,
        if R.source ∉ cluster ∧ R.target ∉ cluster then (cluster.card : ℝ) else 0 := by
    simp only [internalClusterMass, internalClusterFamily, Nat.cast_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_zero]
  constructor
  · rw [hinternal]
    apply Finset.sum_le_sum
    intro cluster _
    split
    · exact le_rfl
    · exact Nat.cast_nonneg _
  · have hpoint (cluster : Finset (Fin vertices)) :
        (R.clusterRadiusRootCount cluster radius : ℝ) ≤
          (if R.source ∉ cluster ∧ R.target ∉ cluster then (R.clusterRadiusRootCount cluster radius : ℝ) else 0) +
          (cluster.card - (if R.source ∉ cluster ∧ R.target ∉ cluster then (cluster.card : ℝ) else 0)) := by
      split_ifs with hi
      · simp
      · simpa using (show (R.clusterRadiusRootCount cluster radius : ℝ) ≤ cluster.card by
          exact_mod_cast R.clusterRadiusRootCount_le_card cluster radius)
    have hsum := Finset.sum_le_sum (fun cluster (_ : cluster ∈ R.clusterFamily configuration) => hpoint cluster)
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← hinternal, ← hmass, R.sum_cluster_card] at hsum
    have hpartition := R.internalClusterMass_partition configuration
    linarith

theorem uniformVertexRadiusTailProbability_boundary_bounds {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (radius : ℕ) :
    0 ≤ R.uniformVertexRadiusTailProbability p radius - R.expectedInternalRadiusRootCount p radius / vertices ∧
      R.uniformVertexRadiusTailProbability p radius - R.expectedInternalRadiusRootCount p radius / vertices ≤
        (R.expectedInternalBoundaryMass p + 2) / vertices := by
  have hvolume : (0 : ℝ) < vertices := by
    have := R.two_le_vertices
    exact_mod_cast (show 0 < vertices by omega)
  have hlo : R.expectedInternalRadiusRootCount p radius ≤
      ∑ configuration, bernoulliWeight p configuration *
        ∑ root : Fin vertices, if radius ≤ R.rootClusterRadius configuration root then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro configuration _
    exact mul_le_mul_of_nonneg_left (R.radiusRootCount_boundary_bounds configuration radius).1
      (bernoulliWeight_nonneg hp hp' configuration)
  have hhi : (∑ configuration, bernoulliWeight p configuration *
      ∑ root : Fin vertices, if radius ≤ R.rootClusterRadius configuration root then (1 : ℝ) else 0) ≤
        R.expectedInternalRadiusRootCount p radius + R.expectedInternalBoundaryMass p + 2 := by
    calc
      _ ≤ ∑ configuration, bernoulliWeight p configuration *
          ((R.internalRadiusRootCount configuration radius : ℝ) + R.internalSelectedMass true true configuration + 2) := by
        apply Finset.sum_le_sum
        intro configuration _
        exact mul_le_mul_of_nonneg_left (R.radiusRootCount_boundary_bounds configuration radius).2
          (bernoulliWeight_nonneg hp hp' configuration)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]
        rfl
  unfold uniformVertexRadiusTailProbability
  rw [← sub_div]
  exact ⟨div_nonneg (sub_nonneg.mpr hlo) hvolume.le,
    div_le_div_of_nonneg_right (by linarith) hvolume.le⟩

end
end Universality.FiniteNetwork
