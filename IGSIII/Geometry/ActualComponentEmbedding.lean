import IGSIII.Geometry.ActualComponentSelection

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The original parent mask restricts to the original child mask, on the
actual finite graph. The equality keeps the same raw noncrossing configuration. -/
theorem generationCellEmbedding_selectedActive_marked (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState)
    (edge : Fin rule.edges) (vertex : Fin (rule.generation depth).vertices) :
    (rule.generation (depth + 1)).network.selectedActive parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened)
      ((rule.generationCellEmbedding depth edge).vertex vertex) =
    (rule.generation depth).network.selectedActive
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) edge).sourceSelected
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) edge).targetSelected
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, parent.massOpened) edge)) vertex := by
  have coarse : (rule.generation depth).network.coarseConfiguration
      (fun edge => markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, parent.massOpened) edge)) =
        marks (address, parent.massOpened) := by
    funext edge
    exact markedGenerationConfiguration_crosses rule marks crossing depth _ _
  rw [← (rule.generationTopDecomposition depth).selectedActive parent.sourceSelected parent.targetSelected]
  change (rule.network.substitute (rule.generation depth).network).selectedActive parent.sourceSelected parent.targetSelected
    ((rule.generationTopDecomposition depth).configuration (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened))
    ((rule.generationTopDecomposition depth).vertex ((rule.generationCellEmbedding depth edge).vertex vertex)) = _
  have configuration_identity : (rule.generationTopDecomposition depth).configuration
      (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened) =
        substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks depth
          (address ++ [edge]) (marks (address, parent.massOpened) edge)) := by
    simp only [markedGenerationConfiguration, Equiv.apply_symm_apply]
  have vertex_identity : (rule.generationTopDecomposition depth).vertex ((rule.generationCellEmbedding depth edge).vertex vertex) =
      Fintype.equivFin _ (rule.network.cellVertex (rule.generation depth).network edge vertex) := by
    exact Equiv.apply_symm_apply _ _
  rw [configuration_identity, vertex_identity, rule.network.selectedActive_substitute_cell, coarse]
  simp only [orientedChildState, orientedStateOf_sourceSelected, orientedStateOf_targetSelected]

theorem live_split_child_original_live (parent : OrientedState) (side : Bool)
    (live : componentChildState parent side ≠ .inactive) : parent ≠ .inactive := by
  intro inactive
  cases side <;> simp_all [componentChildState]

theorem live_split_child_massOpened (parent : OrientedState) (side : Bool)
    (live : componentChildState parent side ≠ .inactive) :
    (componentChildState parent side).massOpened = parent.massOpened := by
  cases parent <;> cases side <;> simp_all [componentChildState, OrientedState.massOpened]

/-- A live split child uses exactly the raw crossing bit of its actual edge. -/
theorem live_component_child_crossing_bit {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (source_selected target_selected : Bool) (edge : Fin edges) (side : Bool)
    (live : componentChildState (network.orientedChildState source_selected target_selected configuration edge) side ≠ .inactive) :
    (componentChildState (network.orientedChildState source_selected target_selected configuration edge) side).massOpened = configuration edge := by
  rw [live_split_child_massOpened _ _ live]
  apply Bool.eq_iff_iff.mpr
  simp only [OrientedState.massOpened, decide_eq_true_eq]
  exact network.live_oriented_state_determines_crossing source_selected target_selected configuration edge
    (live_split_child_original_live _ _ live)

/-- Every selected point of either original B side is retained under the
actual parent mask after embedding the child cell. -/
theorem embedded_split_component_selected (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState)
    (edge : Fin rule.edges) (side : Bool)
    (live : componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
      (marks (address, parent.massOpened)) edge) side ≠ .inactive)
    (vertex : Fin (rule.generation depth).vertices)
    (selected : (rule.generation depth).network.selectedActive
      (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) edge) side).sourceSelected
      (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) edge) side).targetSelected
      (markedGenerationConfiguration rule marks depth (address ++ [edge])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) edge) side).massOpened) vertex = true) :
    (rule.generation (depth + 1)).network.selectedActive parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened)
      ((rule.generationCellEmbedding depth edge).vertex vertex) = true := by
  rw [generationCellEmbedding_selectedActive_marked rule marks crossing]
  rw [live_component_child_crossing_bit rule.network _ _ _ _ _ live] at selected
  exact split_component_selection_implies_original (rule.generation depth).network _ _ _ _ selected

end
end IGSIII.Geometry
