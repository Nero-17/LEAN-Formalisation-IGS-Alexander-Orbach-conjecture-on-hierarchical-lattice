import Universality.Graph.InternalCellNeighborhood
import Universality.Graph.InteriorDecomposition

namespace Universality.FiniteNetwork
noncomputable section

theorem cell_embedding_internal {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (edge : Fin outerEdges) (vertex : S.InteriorVertex) :
    (R.cellNetworkEmbedding S edge).vertex vertex.val ≠ (R.substitute S).source ∧
    (R.cellNetworkEmbedding S edge).vertex vertex.val ≠ (R.substitute S).target := by
  constructor
  · intro heq
    change Fintype.equivFin _ (R.cellVertex S edge vertex.val) =
      Fintype.equivFin _ (Sum.inl R.source) at heq
    have h := (Fintype.equivFin _).injective heq
    rw [R.cellVertex_eq_interior S edge vertex] at h
    cases h
  · intro heq
    change Fintype.equivFin _ (R.cellVertex S edge vertex.val) =
      Fintype.equivFin _ (Sum.inl R.target) at heq
    have h := (Fintype.equivFin _).injective heq
    rw [R.cellVertex_eq_interior S edge vertex] at h
    cases h

theorem NetworkEmbedding.trans_equivalence_incident_edges
    {vR eR vS eS vT eT : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
    {T : FiniteNetwork vT eT} (embedding : R.NetworkEmbedding S)
    (equivalence : S.NetworkEquivalence T) (vertex : Fin vR)
    (hincident : ∀ bond, (S.endpoint bond).1 = embedding.vertex vertex ∨
      (S.endpoint bond).2 = embedding.vertex vertex → ∃ child, embedding.edge child = bond)
    (bond : Fin eT)
    (hbond : (T.endpoint bond).1 = (embedding.trans (.ofEquivalence equivalence)).vertex vertex ∨
      (T.endpoint bond).2 = (embedding.trans (.ofEquivalence equivalence)).vertex vertex) :
    ∃ child, (embedding.trans (.ofEquivalence equivalence)).edge child = bond := by
  have hendpoint := equivalence.endpoint (equivalence.edge.symm bond)
  simp only [Equiv.apply_symm_apply] at hendpoint
  have hback : (S.endpoint (equivalence.edge.symm bond)).1 = embedding.vertex vertex ∨
      (S.endpoint (equivalence.edge.symm bond)).2 = embedding.vertex vertex := by
    rcases hbond with h | h
    · left
      apply equivalence.vertex.injective
      exact (congrArg Prod.fst hendpoint).symm.trans h
    · right
      apply equivalence.vertex.injective
      exact (congrArg Prod.snd hendpoint).symm.trans h
  obtain ⟨child, hchild⟩ := hincident (equivalence.edge.symm bond) hback
  refine ⟨child, ?_⟩
  change equivalence.edge (embedding.edge child) = bond
  rw [hchild, Equiv.apply_symm_apply]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem generationCellEmbedding_internal (rule : Rule) (depth : ℕ) (edge : Fin rule.edges)
    (vertex : (rule.generation depth).network.InteriorVertex) :
    (rule.generationCellEmbedding depth edge).vertex vertex.val ≠ (rule.generation (depth + 1)).network.source ∧
    (rule.generationCellEmbedding depth edge).vertex vertex.val ≠ (rule.generation (depth + 1)).network.target := by
  let inside : (rule.network.substitute (rule.generation depth).network).InteriorVertex :=
    ⟨(rule.network.cellNetworkEmbedding (rule.generation depth).network edge).vertex vertex.val,
      rule.network.cell_embedding_internal (rule.generation depth).network edge vertex⟩
  exact ((rule.generationTopDecomposition depth).symm.mapInterior inside).property

theorem generationCellEmbedding_internal_incident (rule : Rule) (depth : ℕ) (edge : Fin rule.edges)
    (vertex : (rule.generation depth).network.InteriorVertex) (bond : Fin (rule.generation (depth + 1)).edges)
    (hbond : ((rule.generation (depth + 1)).network.endpoint bond).1 =
        (rule.generationCellEmbedding depth edge).vertex vertex.val ∨
      ((rule.generation (depth + 1)).network.endpoint bond).2 =
        (rule.generationCellEmbedding depth edge).vertex vertex.val) :
    ∃ child, (rule.generationCellEmbedding depth edge).edge child = bond :=
  (rule.network.cellNetworkEmbedding (rule.generation depth).network edge).trans_equivalence_incident_edges
    (rule.generationTopDecomposition depth).symm vertex.val
    (rule.network.cell_internal_incident_edge (rule.generation depth).network edge vertex) bond hbond

theorem generationCellEmbedding_internal_neighbor (rule : Rule) (depth : ℕ) (edge : Fin rule.edges)
    (vertex : (rule.generation depth).network.InteriorVertex)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (neighbor : Fin (rule.generation (depth + 1)).vertices)
    (hadj : ((rule.generation (depth + 1)).network.openGraph configuration).Adj
      ((rule.generationCellEmbedding depth edge).vertex vertex.val) neighbor) :
    ∃ inside, (rule.generationCellEmbedding depth edge).vertex inside = neighbor ∧
      ((rule.generation depth).network.openGraph
        ((rule.generationCellEmbedding depth edge).restrict configuration)).Adj vertex.val inside :=
  (rule.generationCellEmbedding depth edge).neighbor_lifts_of_incident_edges vertex.val
    (rule.generationCellEmbedding_internal_incident depth edge vertex) configuration neighbor hadj

end
end Universality.Rule
