import Universality.Percolation.InternalClusterChoices

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- Count each internal component once, at its least vertex. This avoids
repeated equality tests between finite sets in certified finite enumeration. -/
theorem internalClusterFamily_card_representatives (configuration : Configuration edges) :
    (R.internalClusterFamily configuration).card =
      (Finset.univ.filter fun root : Fin vertices =>
        R.source ∉ R.clusterVertices configuration root ∧
        R.target ∉ R.clusterVertices configuration root ∧
        ∀ vertex ∈ R.clusterVertices configuration root, root ≤ vertex).card := by
  classical
  symm
  apply Finset.card_bij (fun root _ => R.clusterVertices configuration root)
  · intro root hroot
    obtain ⟨_, hs, ht, hmin⟩ := Finset.mem_filter.mp hroot
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩, hs, ht⟩
  · intro first hfirst second hsecond heq
    have hminFirst := (Finset.mem_filter.mp hfirst).2.2.2
    have hminSecond := (Finset.mem_filter.mp hsecond).2.2.2
    apply le_antisymm
    · apply hminFirst
      rw [heq]
      exact R.root_mem_clusterVertices configuration second
    · apply hminSecond
      rw [← heq]
      exact R.root_mem_clusterVertices configuration first
  · intro cluster hcluster
    obtain ⟨hfamily, hs, ht⟩ := Finset.mem_filter.mp hcluster
    have hnonempty := Finset.card_pos.mp (R.cluster_card_pos configuration cluster hfamily)
    have heq := R.clusterVertices_eq_of_mem configuration cluster hfamily (cluster.min' hnonempty)
      (Finset.min'_mem _ _)
    refine ⟨cluster.min' hnonempty, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    rw [heq]
    exact ⟨hs, ht, fun vertex hvertex => Finset.min'_le _ vertex hvertex⟩

end
end Universality.FiniteNetwork
