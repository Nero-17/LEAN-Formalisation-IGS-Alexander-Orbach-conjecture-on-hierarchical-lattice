import Universality.Graph.NetworkEmbedding
import Universality.Graph.SubstitutionSimple

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- No edge outside a child cell is incident to one of its internal vertices. -/
theorem cell_internal_incident_edge (edge : Fin outerEdges) (vertex : S.InteriorVertex)
    (bond : Fin (outerEdges * innerEdges))
    (hincident : ((R.substitute S).endpoint bond).1 = (R.cellNetworkEmbedding S edge).vertex vertex.val ∨
      ((R.substitute S).endpoint bond).2 = (R.cellNetworkEmbedding S edge).vertex vertex.val) :
    ∃ child : Fin innerEdges, (R.cellNetworkEmbedding S edge).edge child = bond := by
  obtain ⟨⟨other, child⟩, rfl⟩ := finProdFinEquiv.surjective bond
  simp only [R.substitute_endpoint] at hincident
  have hsame : edge = other := by
    rcases hincident with h | h
    · have heq := (Fintype.equivFin (R.SubstitutionVertex S)).injective h
      exact R.cellVertex_eq_forces_same_cell S vertex.property.1 vertex.property.2 heq.symm
    · have heq := (Fintype.equivFin (R.SubstitutionVertex S)).injective h
      exact R.cellVertex_eq_forces_same_cell S vertex.property.1 vertex.property.2 heq.symm
  subst other
  exact ⟨child, rfl⟩

namespace NetworkEmbedding
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}

theorem neighbor_lifts_of_incident_edges (embedding : R.NetworkEmbedding S)
    (vertex : Fin vR)
    (hincident : ∀ bond, (S.endpoint bond).1 = embedding.vertex vertex ∨
      (S.endpoint bond).2 = embedding.vertex vertex → ∃ child, embedding.edge child = bond)
    (configuration : Configuration eS) (neighbor : Fin vS)
    (hadj : (S.openGraph configuration).Adj (embedding.vertex vertex) neighbor) :
    ∃ inside : Fin vR, embedding.vertex inside = neighbor ∧
      (R.openGraph (embedding.restrict configuration)).Adj vertex inside := by
  obtain ⟨hne, bond, hopen, hpair | hpair⟩ := hadj
  · obtain ⟨child, rfl⟩ := hincident bond (Or.inl (congrArg Prod.fst hpair))
    rw [embedding.endpoint] at hpair
    have hfirst : (R.endpoint child).1 = vertex := embedding.vertex.injective (congrArg Prod.fst hpair)
    refine ⟨(R.endpoint child).2, congrArg Prod.snd hpair, ?_⟩
    refine ⟨?_, child, hopen, Or.inl ?_⟩
    · intro h
      apply hne
      exact (congrArg embedding.vertex h).trans (congrArg Prod.snd hpair)
    · exact Prod.ext hfirst rfl
  · obtain ⟨child, rfl⟩ := hincident bond (Or.inr (congrArg Prod.snd hpair))
    rw [embedding.endpoint] at hpair
    have hsecond : (R.endpoint child).2 = vertex := embedding.vertex.injective (congrArg Prod.snd hpair)
    refine ⟨(R.endpoint child).1, congrArg Prod.fst hpair, ?_⟩
    refine ⟨?_, child, hopen, Or.inr ?_⟩
    · intro h
      apply hne
      exact (congrArg embedding.vertex h).trans (congrArg Prod.fst hpair)
    · exact Prod.ext rfl hsecond

end NetworkEmbedding

theorem cell_internal_neighbor (edge : Fin outerEdges) (vertex : S.InteriorVertex)
    (configuration : Configuration (outerEdges * innerEdges)) (neighbor : Fin (Fintype.card (R.SubstitutionVertex S)))
    (hadj : ((R.substitute S).openGraph configuration).Adj
      ((R.cellNetworkEmbedding S edge).vertex vertex.val) neighbor) :
    ∃ inside : Fin innerVertices, (R.cellNetworkEmbedding S edge).vertex inside = neighbor ∧
      (S.openGraph ((R.cellNetworkEmbedding S edge).restrict configuration)).Adj vertex.val inside :=
  (R.cellNetworkEmbedding S edge).neighbor_lifts_of_incident_edges vertex.val
    (R.cell_internal_incident_edge S edge vertex) configuration neighbor hadj

end
end Universality.FiniteNetwork
