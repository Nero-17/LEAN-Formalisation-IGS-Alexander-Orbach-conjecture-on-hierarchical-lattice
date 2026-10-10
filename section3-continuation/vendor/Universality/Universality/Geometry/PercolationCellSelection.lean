import Universality.Geometry.PercolationClusterVertices
import Universality.Percolation.MassEquivalence

namespace Universality.Rule
noncomputable section
open FiniteNetwork Set
set_option backward.isDefEq.respectTransparency false

/-- The actual configurations inside the first-level cells, with the original edge labels. -/
def percolationCellConfiguration (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (edge : Fin rule.edges) : Configuration (rule.generation depth).edges :=
  substitutionConfigurationEquiv.symm
    ((rule.generationTopDecomposition depth).configuration configuration) edge

def percolationCellState (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (sourceSelected targetSelected : Bool) (edge : Fin rule.edges) : OrientedState :=
  rule.network.orientedChildState sourceSelected targetSelected
    ((rule.generation depth).network.coarseConfiguration
      (rule.percolationCellConfiguration depth configuration)) edge

/-- Pointwise identification with the genuine local terminal-selected percolation cluster. -/
theorem percolationCell_selectedActive (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (sourceSelected targetSelected : Bool) (edge : Fin rule.edges)
    (vertex : Fin (rule.generation depth).vertices) :
    ((rule.generation (depth + 1)).network).selectedActive sourceSelected targetSelected
      configuration ((rule.generationCellEmbedding depth edge).vertex vertex) =
    (rule.generation depth).network.selectedActive
      (rule.percolationCellState depth configuration sourceSelected targetSelected edge).sourceSelected
      (rule.percolationCellState depth configuration sourceSelected targetSelected edge).targetSelected
      (rule.percolationCellConfiguration depth configuration edge) vertex := by
  have hequivalence := (rule.generationTopDecomposition depth).selectedActive
    sourceSelected targetSelected configuration
    ((rule.generationCellEmbedding depth edge).vertex vertex)
  change (rule.network.substitute (rule.generation depth).network).selectedActive
    sourceSelected targetSelected ((rule.generationTopDecomposition depth).configuration configuration)
    ((rule.generationTopDecomposition depth).vertex
      ((rule.generationTopDecomposition depth).vertex.symm
        (Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge vertex)))) = _
    at hequivalence
  rw [Equiv.apply_symm_apply] at hequivalence
  rw [← hequivalence]
  have hconfiguration : (rule.generationTopDecomposition depth).configuration configuration =
      substitutionConfigurationEquiv (rule.percolationCellConfiguration depth configuration) :=
    (substitutionConfigurationEquiv.apply_symm_apply _).symm
  rw [hconfiguration, selectedActive_substitute_cell]
  simp only [percolationCellState, orientedChildState, orientedStateOf_sourceSelected,
    orientedStateOf_targetSelected, percolationCellConfiguration]

def percolationSelectedVertices {rule : Rule} (h : rule.Classical) (depth : ℕ)
    (configuration : Configuration (rule.generation depth).edges)
    (sourceSelected targetSelected : Bool) : Set (GenerationMetricSpace h) :=
  generationMetricVertex h depth ''
    {vertex | (rule.generation depth).network.selectedActive sourceSelected targetSelected
      configuration vertex = true}

theorem percolationSelectedVertices_source {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) (depth : ℕ) :
    percolationSelectedVertices h depth (configuration depth) true false =
      percolationClusterVertices h configuration depth := by
  simp only [percolationSelectedVertices, percolationClusterVertices, selectedActive,
    Bool.true_and, Bool.false_and, Bool.or_false, SimpleGraph.reachableDecide_eq_true]

/-- The finite graph-directed equation uses the actual similarity maps and actual cell states. -/
theorem percolationSelectedVertices_recursion {rule : Rule} (h : rule.Classical) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (sourceSelected targetSelected : Bool) :
    percolationSelectedVertices h (depth + 1) configuration sourceSelected targetSelected =
      ⋃ edge : Fin rule.edges, generationMetricCell h edge ''
        percolationSelectedVertices h depth
          (rule.percolationCellConfiguration depth configuration edge)
          (rule.percolationCellState depth configuration sourceSelected targetSelected edge).sourceSelected
          (rule.percolationCellState depth configuration sourceSelected targetSelected edge).targetSelected := by
  ext point
  constructor
  · rintro ⟨vertex, hvertex, rfl⟩
    obtain ⟨edge, child, rfl⟩ := h.generation_exists_cell_vertex depth vertex
    refine mem_iUnion.mpr ⟨edge, _, ⟨child, ?_, rfl⟩, generationMetricCell_vertex h edge depth child⟩
    exact (rule.percolationCell_selectedActive depth configuration sourceSelected targetSelected edge child).symm.trans hvertex
  · intro hpoint
    obtain ⟨edge, child, ⟨vertex, hvertex, rfl⟩, rfl⟩ := mem_iUnion.mp hpoint
    refine ⟨(rule.generationCellEmbedding depth edge).vertex vertex, ?_,
      (generationMetricCell_vertex h edge depth vertex).symm⟩
    exact (rule.percolationCell_selectedActive depth configuration sourceSelected targetSelected edge vertex).trans hvertex

end
end Universality.Rule
