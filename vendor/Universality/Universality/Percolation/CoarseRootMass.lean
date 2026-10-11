import Universality.Percolation.BirthClusters
import Universality.Percolation.InternalVertexMass

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def rootChildState (R : FiniteNetwork vertices edges) (root : Fin vertices)
    (coarse : Configuration edges) (edge : Fin edges) : OrientedState :=
  orientedStateOf ((R.openGraph coarse).reachableDecide root (R.endpoint edge).1)
    ((R.openGraph coarse).reachableDecide root (R.endpoint edge).2) (coarse edge)

theorem rootChildState_selected (R : FiniteNetwork vertices edges)
    (root : Fin vertices) (coarse : Configuration edges) (edge : Fin edges) :
    (R.rootChildState root coarse edge).sourceSelected =
      (R.openGraph coarse).reachableDecide root (R.endpoint edge).1 ∧
    (R.rootChildState root coarse edge).targetSelected =
      (R.openGraph coarse).reachableDecide root (R.endpoint edge).2 := by
  simp [rootChildState, orientedStateOf_sourceSelected, orientedStateOf_targetSelected]

theorem clusterVertices_card_eq_sum (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (root : Fin vertices) :
    (R.clusterVertices configuration root).card =
      ∑ vertex : Fin vertices, if (R.openGraph configuration).reachableDecide root vertex then 1 else 0 := by
  simp only [clusterVertices, Finset.card_eq_sum_ones, Finset.sum_filter]

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Exact mass of a fine cluster containing a specified old vertex. -/
theorem coarseRoot_cluster_mass (configuration : Fin outerEdges → Configuration innerEdges)
    (root : Fin outerVertices) :
    ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card =
    (R.clusterVertices (S.coarseConfiguration configuration) root).card +
      ∑ edge, S.internalStateMass (R.rootChildState root (S.coarseConfiguration configuration) edge)
        (configuration edge) := by
  rw [(R.substitute S).clusterVertices_card_eq_sum,
    ← (Fintype.equivFin (R.SubstitutionVertex S)).sum_comp]
  change (∑ vertex : Fin outerVertices ⊕ (Fin outerEdges × S.InteriorVertex), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, R.clusterVertices_card_eq_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro vertex _
    have heq : ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).reachableDecide
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl vertex)) =
        (R.openGraph (S.coarseConfiguration configuration)).reachableDecide root vertex := by
      apply Bool.eq_iff_iff.mpr
      simp only [SimpleGraph.reachableDecide_eq_true, R.substitute_reachable_iff S,
        R.substitutedReachable_iff S]
    rw [heq]
  · apply Finset.sum_congr rfl
    intro edge _
    unfold internalStateMass internalSelectedMass
    apply Finset.sum_congr rfl
    intro vertex _
    have heq : ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).reachableDecide
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (edge, vertex))) =
        S.selectedActive (R.rootChildState root (S.coarseConfiguration configuration) edge).sourceSelected
          (R.rootChildState root (S.coarseConfiguration configuration) edge).targetSelected
          (configuration edge) vertex.val := by
      apply Bool.eq_iff_iff.mpr
      simp only [SimpleGraph.reachableDecide_eq_true, R.substitute_reachable_iff S,
        R.substitutedReachable_iff_active S, substitutionActive,
        rootChildState, orientedStateOf_sourceSelected, orientedStateOf_targetSelected,
        selectedActive, Bool.or_eq_true, Bool.and_eq_true, SimpleGraph.reachableDecide_eq_true]
    rw [heq]

/-- The birth indicator of a coarse-root cluster is decided entirely on the coarse graph. -/
theorem coarseRoot_cluster_mem_birth_iff
    (configuration : Fin outerEdges → Configuration innerEdges) (root : Fin outerVertices) :
    (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) ∈ R.birthClusterFamily S configuration ↔
    R.source ∉ R.clusterVertices (S.coarseConfiguration configuration) root ∧
      R.target ∉ R.clusterVertices (S.coarseConfiguration configuration) root := by
  have hfamily : (R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root)) ∈
      (R.substitute S).clusterFamily (substitutionConfigurationEquiv configuration) :=
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hcoarse : ¬ Disjoint ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))) (R.coarseVertices S) := by
    intro hdisjoint
    exact Finset.disjoint_left.mp hdisjoint
      ((R.substitute S).root_mem_clusterVertices _ _)
      (Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩)
  simp only [birthClusterFamily, internalClusterFamily, Finset.mem_filter, hfamily, hcoarse,
    not_false_eq_true, and_true, true_and]
  change (_ ∉ (R.substitute S).clusterVertices _ _ ∧ _ ∉ (R.substitute S).clusterVertices _ _) ↔ _
  simp only [mem_clusterVertices]
  change (¬ ((R.substitute S).openGraph _).Reachable
    (Fintype.equivFin _ (Sum.inl root)) (Fintype.equivFin _ (Sum.inl R.source)) ∧
    ¬ ((R.substitute S).openGraph _).Reachable
    (Fintype.equivFin _ (Sum.inl root)) (Fintype.equivFin _ (Sum.inl R.target))) ↔ _
  simp only [R.substitute_reachable_iff S, R.substitutedReachable_iff S]

end
end Universality.FiniteNetwork


