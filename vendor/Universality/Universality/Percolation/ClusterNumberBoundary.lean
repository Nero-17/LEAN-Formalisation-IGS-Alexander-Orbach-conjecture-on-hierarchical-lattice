import Universality.Percolation.ClusterNumberRecursion

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem boundaryClusterFamily_eq_pair (configuration : Configuration edges) :
    R.boundaryClusterFamily configuration =
      {R.clusterVertices configuration R.source, R.clusterVertices configuration R.target} := by
  ext cluster
  constructor
  · intro hcluster
    obtain ⟨hfamily, hsource | htarget⟩ := Finset.mem_filter.mp hcluster
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (R.clusterVertices_eq_of_mem configuration cluster hfamily R.source hsource).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (R.clusterVertices_eq_of_mem configuration cluster hfamily R.target htarget).symm
  · intro hcluster
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcluster
    rcases hcluster with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨R.source, Finset.mem_univ _, rfl⟩,
        Or.inl (R.root_mem_clusterVertices configuration R.source)⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨R.target, Finset.mem_univ _, rfl⟩,
        Or.inr (R.root_mem_clusterVertices configuration R.target)⟩

theorem boundaryClusterFamily_card (configuration : Configuration edges) :
    (R.boundaryClusterFamily configuration).card = if R.crosses configuration then 1 else 2 := by
  rw [R.boundaryClusterFamily_eq_pair]
  by_cases hcross : R.crosses configuration = true
  · have heq := (R.clusterVertices_eq_iff configuration R.source R.target).mpr ((R.crosses_eq_true _).mp hcross)
    simp [hcross, heq]
  · have hne : R.clusterVertices configuration R.source ≠ R.clusterVertices configuration R.target := by
      intro heq
      exact hcross ((R.crosses_eq_true _).mpr ((R.clusterVertices_eq_iff _ _ _).mp heq))
    simp [hcross, hne]

theorem clusterFamily_card_boundary_correction (configuration : Configuration edges) :
    ((R.clusterFamily configuration).card : ℝ) =
      (R.internalClusterFamily configuration).card + 2 - (if R.crosses configuration then 1 else 0) := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := R.clusterFamily configuration)
    (p := fun cluster => R.source ∉ cluster ∧ R.target ∉ cluster)
  have hfilter : ((R.clusterFamily configuration).filter
      fun cluster => ¬ (R.source ∉ cluster ∧ R.target ∉ cluster)) = R.boundaryClusterFamily configuration := by
    ext cluster
    simp only [boundaryClusterFamily, Finset.mem_filter]
    rw [not_and_or]
    simp only [not_not]
  change (R.internalClusterFamily configuration).card + _ = (R.clusterFamily configuration).card at hsplit
  rw [hfilter, R.boundaryClusterFamily_card] at hsplit
  have hreal := congrArg (fun value : ℕ => (value : ℝ)) hsplit
  push_cast at hreal
  split_ifs at hreal ⊢ <;> linarith

theorem expectedClusterNumber_boundary_correction (p : ℝ) :
    R.expectedClusterNumber p = R.expectedInternalClusterNumber p + 2 - R.reliability p := by
  unfold expectedClusterNumber expectedInternalClusterNumber
  simp_rw [R.clusterFamily_card_boundary_correction, mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_bernoulliWeight, one_mul]
  congr 1
  simp only [reliability, mul_ite, mul_one, mul_zero]

end
end Universality.FiniteNetwork
