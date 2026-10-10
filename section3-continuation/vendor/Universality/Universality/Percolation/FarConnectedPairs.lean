import Universality.Percolation.InternalClusterDecomposition
import Universality.Graph.CellIsometry
import Universality.Percolation.CoarseRootMoments

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Ordered connected pairs separated by more than a deterministic distance. -/
def farConnectedPairs (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (distance : ℕ) :
    Finset (Fin vertices × Fin vertices) := by
  classical
  exact Finset.univ.filter fun pair => distance < R.fullGraph.dist pair.1 pair.2 ∧
    (R.openGraph configuration).Reachable pair.1 pair.2

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- A connected pair farther apart than any child diameter must belong to a
component meeting the coarse skeleton. -/
theorem far_pair_cluster_meets_coarse
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (first second : Fin (Fintype.card (R.SubstitutionVertex S)))
    (hfar : diameter < (R.substitute S).fullGraph.dist first second)
    (hconnected : ((R.substitute S).openGraph
      (substitutionConfigurationEquiv configuration)).Reachable first second) :
    ¬ Disjoint ((R.substitute S).clusterVertices
      (substitutionConfigurationEquiv configuration) first) (R.coarseVertices S) := by
  intro hdisjoint
  obtain ⟨edge, child, _, _, _, heq⟩ :=
    R.cluster_avoiding_coarse_is_internal_cell S configuration _
      (Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩) hdisjoint
  have hfirst := (R.substitute S).root_mem_clusterVertices
    (substitutionConfigurationEquiv configuration) first
  have hsecond := ((R.substitute S).mem_clusterVertices _ first second).mpr hconnected
  rw [heq] at hfirst hsecond
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hfirst
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hsecond
  have hdist := R.substitute_cell_distance S hinner edge u v
  change (R.substitute S).fullGraph.dist (R.cellEmbedding S edge u)
    (R.cellEmbedding S edge v) = S.fullGraph.dist u v at hdist
  rw [hdist] at hfar
  exact (not_lt_of_ge (hdiameter u v)) hfar

/-- Counting coarse-root squares may overcount a component, but dominates
every connected ordered pair exceeding the child diameter. -/
theorem farConnectedPairs_card_le_coarse_root_squares
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    (configuration : Fin outerEdges → Configuration innerEdges) :
    ((R.substitute S).farConnectedPairs (substitutionConfigurationEquiv configuration) diameter).card ≤
      ∑ root : Fin outerVertices,
        ((R.substitute S).clusterVertices (substitutionConfigurationEquiv configuration)
          (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card ^ 2 := by
  classical
  let cluster (root : Fin outerVertices) := (R.substitute S).clusterVertices
    (substitutionConfigurationEquiv configuration)
    (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))
  have hsubset : (R.substitute S).farConnectedPairs
      (substitutionConfigurationEquiv configuration) diameter ⊆
      Finset.univ.biUnion (fun root : Fin outerVertices => (cluster root).product (cluster root)) := by
    intro pair hpair
    obtain ⟨hfar, hconnected⟩ := (Finset.mem_filter.mp hpair).2
    have hmeet := R.far_pair_cluster_meets_coarse S hinner diameter hdiameter
      configuration pair.1 pair.2 hfar hconnected
    obtain ⟨vertex, hvertex, hcoarse⟩ := Finset.not_disjoint_iff.mp hmeet
    obtain ⟨root, _, rfl⟩ := Finset.mem_image.mp hcoarse
    have hroot := ((R.substitute S).mem_clusterVertices _ _ _).mp hvertex
    apply Finset.mem_biUnion.mpr
    refine ⟨root, Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact ((R.substitute S).mem_clusterVertices _ _ _).mpr hroot.symm
    · exact ((R.substitute S).mem_clusterVertices _ _ _).mpr (hroot.symm.trans hconnected)
  calc
    _ ≤ (Finset.univ.biUnion (fun root : Fin outerVertices =>
        (cluster root).product (cluster root))).card := Finset.card_le_card hsubset
    _ ≤ ∑ root : Fin outerVertices, ((cluster root).product (cluster root)).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro root _
      exact (Finset.card_product (cluster root) (cluster root)).trans (pow_two _).symm

/-- The actual Bernoulli expectation of all sufficiently separated connected
pairs is controlled by the child boundary second moment. -/
theorem expected_farConnectedPairs_le_boundary_second_moment
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (∑ configuration : Configuration (outerEdges * innerEdges),
      bernoulliWeight p configuration *
        (((R.substitute S).farConnectedPairs configuration diameter).card : ℝ)) ≤
      (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) *
        ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * S.expectedInternalBoundaryMoment p 2) := by
  calc
    _ ≤ ∑ root : Fin outerVertices,
        R.coarseRootMassObservable S p root (fun mass => (mass : ℝ) ^ 2) := by
      unfold coarseRootMassObservable
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro configuration _
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp hp' _)
      have hbound := R.farConnectedPairs_card_le_coarse_root_squares S hinner diameter
        hdiameter (substitutionConfigurationEquiv.symm configuration)
      simp only [Equiv.apply_symm_apply] at hbound
      change (((R.substitute S).farConnectedPairs configuration diameter).card : ℝ) ≤
        ∑ root : Fin outerVertices, (((R.substitute S).clusterVertices configuration
          (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl root))).card : ℝ) ^ 2
      exact_mod_cast hbound
    _ ≤ ∑ _root : Fin outerVertices, ((outerEdges : ℝ) + 1) *
        ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * S.expectedInternalBoundaryMoment p 2) := by
      apply Finset.sum_le_sum
      intro root _
      simpa only [Nat.reduceSub, pow_one] using
        R.coarseRootMassObservable_power_le_boundary_moment S hp hp' root 2 (by omega)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end
end Universality.FiniteNetwork
