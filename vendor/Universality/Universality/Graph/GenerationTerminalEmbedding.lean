import Universality.Graph.GenerationInternalNeighborhood

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem cellNetworkEmbedding_source_eq_source_iff (edge : Fin outerEdges) :
    (R.cellNetworkEmbedding S edge).vertex S.source = (R.substitute S).source ↔
      (R.endpoint edge).1 = R.source := by
  change (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.source) =
    Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.source)) ↔ _
  rw [R.cellVertex_source]
  constructor
  · intro heq
    exact Sum.inl.inj ((Fintype.equivFin (R.SubstitutionVertex S)).injective heq)
  · intro heq
    rw [heq]

theorem cellNetworkEmbedding_source_eq_target_iff (edge : Fin outerEdges) :
    (R.cellNetworkEmbedding S edge).vertex S.source = (R.substitute S).target ↔
      (R.endpoint edge).1 = R.target := by
  change (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.source) =
    Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.target)) ↔ _
  rw [R.cellVertex_source]
  constructor
  · intro heq
    exact Sum.inl.inj ((Fintype.equivFin (R.SubstitutionVertex S)).injective heq)
  · intro heq
    rw [heq]

theorem cellNetworkEmbedding_target_eq_source_iff (edge : Fin outerEdges) :
    (R.cellNetworkEmbedding S edge).vertex S.target = (R.substitute S).source ↔
      (R.endpoint edge).2 = R.source := by
  change (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.target) =
    Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.source)) ↔ _
  rw [R.cellVertex_target]
  constructor
  · intro heq
    exact Sum.inl.inj ((Fintype.equivFin (R.SubstitutionVertex S)).injective heq)
  · intro heq
    rw [heq]

theorem cellNetworkEmbedding_target_eq_target_iff (edge : Fin outerEdges) :
    (R.cellNetworkEmbedding S edge).vertex S.target = (R.substitute S).target ↔
      (R.endpoint edge).2 = R.target := by
  change (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge S.target) =
    Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.target)) ↔ _
  rw [R.cellVertex_target]
  constructor
  · intro heq
    exact Sum.inl.inj ((Fintype.equivFin (R.SubstitutionVertex S)).injective heq)
  · intro heq
    rw [heq]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

theorem generationCellEmbedding_source_eq_source_iff (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.source =
      (rule.generation (depth + 1)).network.source ↔ (rule.network.endpoint edge).1 = rule.network.source := by
  change (rule.generationTopDecomposition depth).vertex.symm
    ((rule.network.cellNetworkEmbedding (rule.generation depth).network edge).vertex
      (rule.generation depth).network.source) = (rule.generation (depth + 1)).network.source ↔ _
  rw [Equiv.symm_apply_eq, (rule.generationTopDecomposition depth).source]
  exact rule.network.cellNetworkEmbedding_source_eq_source_iff (rule.generation depth).network edge

theorem generationCellEmbedding_source_eq_target_iff (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.source =
      (rule.generation (depth + 1)).network.target ↔ (rule.network.endpoint edge).1 = rule.network.target := by
  change (rule.generationTopDecomposition depth).vertex.symm
    ((rule.network.cellNetworkEmbedding (rule.generation depth).network edge).vertex
      (rule.generation depth).network.source) = (rule.generation (depth + 1)).network.target ↔ _
  rw [Equiv.symm_apply_eq, (rule.generationTopDecomposition depth).target]
  exact rule.network.cellNetworkEmbedding_source_eq_target_iff (rule.generation depth).network edge

theorem generationCellEmbedding_target_eq_source_iff (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.target =
      (rule.generation (depth + 1)).network.source ↔ (rule.network.endpoint edge).2 = rule.network.source := by
  change (rule.generationTopDecomposition depth).vertex.symm
    ((rule.network.cellNetworkEmbedding (rule.generation depth).network edge).vertex
      (rule.generation depth).network.target) = (rule.generation (depth + 1)).network.source ↔ _
  rw [Equiv.symm_apply_eq, (rule.generationTopDecomposition depth).source]
  exact rule.network.cellNetworkEmbedding_target_eq_source_iff (rule.generation depth).network edge

theorem generationCellEmbedding_target_eq_target_iff (rule : Rule) (depth : ℕ) (edge : Fin rule.edges) :
    (rule.generationCellEmbedding depth edge).vertex (rule.generation depth).network.target =
      (rule.generation (depth + 1)).network.target ↔ (rule.network.endpoint edge).2 = rule.network.target := by
  change (rule.generationTopDecomposition depth).vertex.symm
    ((rule.network.cellNetworkEmbedding (rule.generation depth).network edge).vertex
      (rule.generation depth).network.target) = (rule.generation (depth + 1)).network.target ↔ _
  rw [Equiv.symm_apply_eq, (rule.generationTopDecomposition depth).target]
  exact rule.network.cellNetworkEmbedding_target_eq_target_iff (rule.generation depth).network edge

end
end Universality.Rule
