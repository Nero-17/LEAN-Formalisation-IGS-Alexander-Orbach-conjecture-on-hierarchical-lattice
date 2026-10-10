import Universality.Geometry.PercolationCellCoherence
import Universality.Geometry.PercolationGromovHausdorff

namespace Universality.Rule
noncomputable section
open FiniteNetwork Set
set_option backward.isDefEq.respectTransparency false

theorem generation_selectedActive_old (rule : Rule) (depth : ℕ)
    (configuration : Configuration (rule.generation (depth + 1)).edges)
    (sourceSelected targetSelected : Bool) (vertex : Fin (rule.generation depth).vertices) :
    (rule.generation (depth + 1)).network.selectedActive sourceSelected targetSelected configuration
      (rule.generationOldVertex depth vertex) =
    (rule.generation depth).network.selectedActive sourceSelected targetSelected
      (rule.coarsenGeneration depth configuration) vertex := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true, SimpleGraph.reachableDecide_eq_true]
  change ((sourceSelected = true ∧
      ((rule.generation (depth + 1)).network.openGraph configuration).Reachable
        (rule.generationOldVertex depth (rule.generation depth).network.source)
        (rule.generationOldVertex depth vertex)) ∨
    (targetSelected = true ∧
      ((rule.generation (depth + 1)).network.openGraph configuration).Reachable
        (rule.generationOldVertex depth (rule.generation depth).network.target)
        (rule.generationOldVertex depth vertex))) ↔ _
  rw [generation_reachable_old_iff, generation_reachable_old_iff]

theorem percolationSelectedVertices_monotone {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n)
    (sourceSelected targetSelected : Bool) :
    Monotone (fun n => percolationSelectedVertices h n (configuration n) sourceSelected targetSelected) := by
  apply monotone_nat_of_le_succ
  intro n point hpoint
  obtain ⟨vertex, hvertex, rfl⟩ := hpoint
  refine ⟨rule.generationOldVertex n vertex, ?_, (generationMetricVertex_old h n vertex).symm⟩
  change (rule.generation (n + 1)).network.selectedActive sourceSelected targetSelected
    (configuration (n + 1)) (rule.generationOldVertex n vertex) = true
  rw [generation_selectedActive_old, hcoarsen]
  exact hvertex

def percolationSelectedLimit {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (sourceSelected targetSelected : Bool) : Set (GenerationMetricSpace h) :=
  closure (⋃ n, percolationSelectedVertices h n (configuration n) sourceSelected targetSelected)

theorem percolationSelectedLimit_source {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges) :
    percolationSelectedLimit h configuration true false = percolationClusterLimit h configuration := by
  simp only [percolationSelectedLimit, percolationClusterLimit, percolationSelectedVertices_source]

/-- Exact graph-directed equation for the closure of actual percolation vertices.
The four live types retain the orientation of the selected terminal; inactive cells give the empty set. -/
theorem percolationSelectedLimit_graphDirected {rule : Rule} (h : rule.Classical)
    (configuration : ∀ n, Configuration (rule.generation n).edges)
    (hcoarsen : ∀ n, rule.coarsenGeneration n (configuration (n + 1)) = configuration n)
    (sourceSelected targetSelected : Bool) :
    percolationSelectedLimit h configuration sourceSelected targetSelected =
      ⋃ edge : Fin rule.edges, generationMetricCell h edge ''
        percolationSelectedLimit h
          (fun n => rule.percolationCellConfiguration n (configuration (n + 1)) edge)
          (rule.network.orientedChildState sourceSelected targetSelected (configuration 0) edge).sourceSelected
          (rule.network.orientedChildState sourceSelected targetSelected (configuration 0) edge).targetSelected := by
  have htail : (⋃ n, percolationSelectedVertices h n (configuration n) sourceSelected targetSelected) =
      ⋃ n, percolationSelectedVertices h (n + 1) (configuration (n + 1)) sourceSelected targetSelected := by
    apply Subset.antisymm
    · intro point hpoint
      obtain ⟨n, hn⟩ := mem_iUnion.mp hpoint
      exact mem_iUnion.mpr ⟨n, percolationSelectedVertices_monotone h configuration hcoarsen
        sourceSelected targetSelected (Nat.le_succ n) hn⟩
    · exact iUnion_mono' (fun n => ⟨n + 1, Subset.rfl⟩)
  unfold percolationSelectedLimit
  rw [htail]
  simp_rw [percolationSelectedVertices_recursion, percolationCellState_eq rule configuration hcoarsen]
  rw [iUnion_comm, closure_iUnion_of_finite]
  congr 1
  funext edge
  rw [← image_iUnion]
  exact (generationMetricCell_continuous h edge).isClosedMap.closure_image_eq_of_continuous
    (generationMetricCell_continuous h edge) _

end
end Universality.Rule
