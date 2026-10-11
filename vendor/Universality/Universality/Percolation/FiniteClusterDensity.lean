import Universality.Percolation.FiniteClusters

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem clusterVertices_eq_of_mem (configuration : Configuration edges)
    (cluster : Finset (Fin vertices)) (hcluster : cluster ∈ R.clusterFamily configuration)
    (root : Fin vertices) (hroot : root ∈ cluster) :
    R.clusterVertices configuration root = cluster := by
  rw [← R.clusterFamily_fiber configuration cluster hcluster] at hroot
  exact (Finset.mem_filter.mp hroot).2

theorem cluster_card_pos (configuration : Configuration edges)
    (cluster : Finset (Fin vertices)) (hcluster : cluster ∈ R.clusterFamily configuration) :
    0 < cluster.card := by
  obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcluster
  exact Finset.card_pos.mpr ⟨root, R.root_mem_clusterVertices configuration root⟩

def boundaryClusterFamily (configuration : Configuration edges) : Finset (Finset (Fin vertices)) :=
  (R.clusterFamily configuration).filter fun cluster => R.source ∈ cluster ∨ R.target ∈ cluster

def internalClusterCount (configuration : Configuration edges) (size : ℕ) : ℕ :=
  ((R.clusterFamily configuration).filter fun cluster =>
    cluster.card = size ∧ R.source ∉ cluster ∧ R.target ∉ cluster).card

theorem boundaryClusterFamily_card_le_two (configuration : Configuration edges) :
    (R.boundaryClusterFamily configuration).card ≤ 2 := by
  have hsubset : R.boundaryClusterFamily configuration ⊆
      {R.clusterVertices configuration R.source, R.clusterVertices configuration R.target} := by
    intro cluster hcluster
    obtain ⟨hfamily, hsource | htarget⟩ := Finset.mem_filter.mp hcluster
    · exact Finset.mem_insert.mpr (Or.inl (R.clusterVertices_eq_of_mem configuration cluster hfamily R.source hsource).symm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (R.clusterVertices_eq_of_mem configuration cluster hfamily R.target htarget).symm))
  apply (Finset.card_le_card hsubset).trans
  by_cases heq : R.clusterVertices configuration R.source = R.clusterVertices configuration R.target
  · simp [heq]
  · simp [heq]

/-- Removing the two outer terminals affects at most two clusters of each size. -/
theorem internalClusterCount_bounds (configuration : Configuration edges) (size : ℕ) :
    R.internalClusterCount configuration size ≤ R.clusterCount configuration size ∧
      R.clusterCount configuration size ≤ R.internalClusterCount configuration size + 2 := by
  classical
  constructor
  · apply Finset.card_le_card
    intro cluster hcluster
    obtain ⟨hfamily, hsize, _⟩ := Finset.mem_filter.mp hcluster
    exact Finset.mem_filter.mpr ⟨hfamily, hsize⟩
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := (R.clusterFamily configuration).filter fun cluster => cluster.card = size)
      (p := fun cluster => R.source ∉ cluster ∧ R.target ∉ cluster)
    have hinternal : (((R.clusterFamily configuration).filter fun cluster => cluster.card = size).filter
        fun cluster => R.source ∉ cluster ∧ R.target ∉ cluster).card =
        R.internalClusterCount configuration size := by simp [internalClusterCount, Finset.filter_filter, and_assoc]
    have hboundary : (((R.clusterFamily configuration).filter fun cluster => cluster.card = size).filter
        fun cluster => ¬ (R.source ∉ cluster ∧ R.target ∉ cluster)).card ≤ 2 := by
      apply le_trans (Finset.card_le_card (t := R.boundaryClusterFamily configuration) ?_)
        (R.boundaryClusterFamily_card_le_two configuration)
      intro cluster hcluster
      change cluster ∈ (R.clusterFamily configuration).filter _
      simp only [Finset.mem_filter] at hcluster ⊢
      exact ⟨hcluster.1.1, by simpa only [not_and_or, not_not] using hcluster.2⟩
    rw [hinternal] at hsplit
    change _ + _ = R.clusterCount configuration size at hsplit
    omega

theorem uniformVertexClusterMassProbability_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (size : ℕ) :
    0 ≤ R.uniformVertexClusterMassProbability p size := by
  unfold uniformVertexClusterMassProbability
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro configuration _
  apply mul_nonneg (bernoulliWeight_nonneg hp hp' configuration)
  exact Finset.sum_nonneg (fun root _ => by split <;> norm_num)

/-- The finite uniform-root cluster-size law has total mass one. -/
theorem sum_uniformVertexClusterMassProbability (p : ℝ) :
    (∑ size ∈ Finset.range (vertices + 1), R.uniformVertexClusterMassProbability p size) = 1 := by
  have hvertices : (vertices : ℝ) ≠ 0 := by
    have h := R.two_le_vertices
    exact_mod_cast (by omega : vertices ≠ 0)
  simp only [uniformVertexClusterMassProbability, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hsum (configuration : Configuration edges) :
      (∑ size ∈ Finset.range (vertices + 1), bernoulliWeight p configuration *
        ∑ root : Fin vertices, if (R.clusterVertices configuration root).card = size then (1 : ℝ) else 0) =
      bernoulliWeight p configuration * vertices := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hcard (root : Fin vertices) : (R.clusterVertices configuration root).card < vertices + 1 :=
      Nat.lt_succ_of_le (by simpa using Finset.card_le_univ (R.clusterVertices configuration root))
    simp [hcard]
  simp_rw [hsum]
  rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul, div_self hvertices]

end
end Universality.FiniteNetwork
