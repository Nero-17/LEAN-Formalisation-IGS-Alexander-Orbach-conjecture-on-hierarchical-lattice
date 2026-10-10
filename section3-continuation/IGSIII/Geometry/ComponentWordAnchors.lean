import IGSIII.Geometry.ActualAddressEmbedding
import IGSIII.Geometry.ActualBirthSkeletonPersistence
import IGSIII.Geometry.ActualBlockComponentLimits
import IGSIII.Chemical.SubstitutionPaths.BlockAddresses

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

def generationWordEdge (rule : Rule) : (depth : ℕ) →
    (Fin (depth + 1) → Fin rule.edges) → Fin (rule.generation depth).edges
  | 0, word => word 0
  | depth + 1, word => (rule.generationTopDecomposition depth).edge.symm
      (finProdFinEquiv (word 0, generationWordEdge rule depth (fun index => word index.succ)))

theorem generationWordEdge_address (rule : Rule) (depth : ℕ) (word : Fin (depth + 1) → Fin rule.edges) :
    generationEdgeAddress rule depth (generationWordEdge rule depth word) = List.ofFn word := by
  induction depth with
  | zero => simp only [generationWordEdge, generationEdgeAddress, List.ofFn_succ, List.ofFn_zero]
  | succ depth induction_hypothesis =>
      rw [generationWordEdge, generationEdgeAddress_top, induction_hypothesis]
      exact (List.ofFn_succ (f := word)).symm

def generationWordVertexEmbedding (rule : Rule) : (depth : ℕ) →
    (Fin (depth + 1) → Fin rule.edges) → rule.network.NetworkEmbedding (rule.generation (depth + 1)).network
  | 0, word => rule.generationCellEmbedding 0 (word 0)
  | depth + 1, word => (generationWordVertexEmbedding rule depth (fun index => word index.succ)).trans
      (rule.generationCellEmbedding (depth + 1) (word 0))

def componentWordAnchor (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) : Fin (rule.generation depth).vertices :=
  if (retainedComponentState rule marks (List.ofFn word)).sourceSelected then
    ((rule.generation depth).network.endpoint (generationWordEdge rule depth (fun index => (word index).1))).1
  else ((rule.generation depth).network.endpoint (generationWordEdge rule depth (fun index => (word index).1))).2

/-- An addressed planting vertex is the genuine persistent coarse-edge
endpoint, with the selected side kept distinct. -/
theorem generationAddressEmbedding_word_planted (rule : Rule) (depth : ℕ)
    (word : Fin (depth + 1) → Fin rule.edges) (source_side : Bool) :
    (generationWordVertexEmbedding rule depth word).vertex (plantedVertex rule.network source_side) =
      rule.generationOldVertex depth (if source_side then
        ((rule.generation depth).network.endpoint (generationWordEdge rule depth word)).1
        else ((rule.generation depth).network.endpoint (generationWordEdge rule depth word)).2) := by
  induction depth with
  | zero =>
      cases source_side <;> simp only [generationWordVertexEmbedding, plantedVertex,
        Bool.false_eq_true, ↓reduceIte, generationWordEdge]
      · exact generationCellEmbedding_target rule 0 (word 0)
      · exact generationCellEmbedding_source rule 0 (word 0)
  | succ depth induction_hypothesis =>
      simp only [generationWordVertexEmbedding, NetworkEmbedding.trans, Function.Embedding.trans_apply]
      rw [induction_hypothesis]
      rw [← rule.generationCellEmbedding_oldVertex]
      congr 1
      have endpoints := (rule.generationCellEmbedding depth (word 0)).endpoint
        (generationWordEdge rule depth (fun index => word index.succ))
      change (rule.generation (depth + 1)).network.endpoint
        (generationWordEdge rule (depth + 1) word) = _ at endpoints
      cases source_side with
      | false => exact (congrArg Prod.snd endpoints).symm
      | true => exact (congrArg Prod.fst endpoints).symm

theorem generationWordVertexEmbedding_selected_component (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (word : Fin (depth + 1) → (Fin rule.edges × Bool))
    (live : retainedComponentStateFrom rule marks ancestor parent (List.ofFn word) ≠ .inactive)
    (vertex : Fin rule.vertices)
    (selected : rule.network.selectedActive
      (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).sourceSelected
      (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).targetSelected
      (marks (ancestor ++ componentEdgeAddress (List.ofFn word),
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).massOpened)) vertex = true) :
    (rule.generation (depth + 1)).network.selectedActive parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) ancestor parent.massOpened)
      ((generationWordVertexEmbedding rule depth (fun index => (word index).1)).vertex vertex) = true := by
  induction depth generalizing ancestor parent with
  | zero =>
      have child_live : componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) (word 0).1) (word 0).2 ≠ .inactive := by
        simpa only [List.ofFn_succ, List.ofFn_zero, retainedComponentStateFrom] using live
      apply embedded_split_component_selected rule marks crossing 0 ancestor parent (word 0).1 (word 0).2 child_live vertex
      simpa only [List.ofFn_succ, List.ofFn_zero, retainedComponentStateFrom, componentEdgeAddress,
        List.map_cons, List.map_nil, markedGenerationConfiguration, Rule.generation] using selected
  | succ depth induction_hypothesis =>
      have child_live := retainedComponentStateFrom_live_parent rule marks (ancestor ++ [(word 0).1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) (word 0).1) (word 0).2)
        (List.ofFn (fun index : Fin (depth + 1) => word index.succ)) (by
          simpa only [List.ofFn_succ, retainedComponentStateFrom] using live)
      have child_selected := induction_hypothesis (ancestor ++ [(word 0).1])
        (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (ancestor, parent.massOpened)) (word 0).1) (word 0).2)
        (fun index => word index.succ) (by simpa only [List.ofFn_succ, retainedComponentStateFrom] using live) (by
          simpa only [List.ofFn_succ, retainedComponentStateFrom, componentEdgeAddress, List.map_cons,
            List.append_assoc, List.singleton_append] using selected)
      exact embedded_split_component_selected rule marks crossing (depth + 1) ancestor parent
        (word 0).1 (word 0).2 child_live _ child_selected

/-- Every live component-word anchor is an actual retained coarse vertex,
before passing to any chemical metric or completion. -/
theorem componentWordAnchor_retained (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive) :
    ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
      (rule.generation depth).network.source (componentWordAnchor rule marks depth word) := by
  have selected : rule.network.selectedActive (retainedComponentState rule marks (List.ofFn word)).sourceSelected
      (retainedComponentState rule marks (List.ofFn word)).targetSelected
      (marks (componentEdgeAddress (List.ofFn word), (retainedComponentState rule marks (List.ofFn word)).massOpened))
      (plantedVertex rule.network (retainedComponentState rule marks (List.ofFn word)).sourceSelected) = true := by
    apply (single_oriented_component_selected_iff rule.network _ _
      (retainedComponentState_ne_both rule marks _) live (crossing _ _) _).mpr
    exact SimpleGraph.Reachable.refl _
  have inherited := generationWordVertexEmbedding_selected_component rule marks crossing depth [] .connected word live _ (by
    simpa only [List.nil_append, retainedComponentState] using selected)
  have retained := (single_oriented_component_selected_iff (rule.generation (depth + 1)).network _ .connected
    (by decide) (by decide) (markedGenerationConfiguration_crosses rule marks crossing (depth + 1) [] true) _).mp inherited
  rw [generationAddressEmbedding_word_planted] at retained
  change ((rule.generation (depth + 1)).network.openGraph
    (markedGenerationConfiguration rule marks (depth + 1) [] true)).Reachable
      (rule.generation (depth + 1)).network.source (rule.generationOldVertex depth (componentWordAnchor rule marks depth word)) at retained
  have source_identity := generationOldVertex_planted rule depth true
  change rule.generationOldVertex depth (rule.generation depth).network.source = (rule.generation (depth + 1)).network.source at source_identity
  rw [← source_identity, rule.generation_reachable_old_iff,
    markedGenerationConfiguration_coarsens rule marks crossing depth [] true] at retained
  exact retained

theorem generationWordEdge_bottom (rule : Rule) (depth : ℕ)
    (word : Fin (depth + 2) → Fin rule.edges) :
    generationWordEdge rule (depth + 1) word =
      finProdFinEquiv (generationWordEdge rule depth (Fin.init word), word (Fin.last (depth + 1))) := by
  apply generationEdgeAddress_injective rule (depth + 1)
  rw [generationWordEdge_address, generationEdgeAddress_bottom, generationWordEdge_address]
  change List.ofFn word = List.ofFn (fun index : Fin (depth + 1) => word index.castSucc) ++ [word (Fin.last (depth + 1))]
  simpa only [List.concat_eq_append] using List.ofFn_succ' (f := word)

theorem componentChildState_selected_endpoint {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (source_selected target_selected : Bool) (edge : Fin edges) (side : Bool)
    (live : componentChildState (network.orientedChildState source_selected target_selected configuration edge) side ≠ .inactive) :
    network.selectedActive source_selected target_selected configuration
      (if (componentChildState (network.orientedChildState source_selected target_selected configuration edge) side).sourceSelected
        then (network.endpoint edge).1 else (network.endpoint edge).2) = true := by
  unfold orientedChildState at live ⊢
  cases first : network.selectedActive source_selected target_selected configuration (network.endpoint edge).1 <;>
    cases last : network.selectedActive source_selected target_selected configuration (network.endpoint edge).2 <;>
      cases configuration edge <;> cases side <;>
        simp_all [orientedStateOf, componentChildState, OrientedState.sourceSelected]

theorem componentWordAnchor_bottom (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (word : Fin (depth + 2) → (Fin rule.edges × Bool)) :
    componentWordAnchor rule marks (depth + 1) word =
      (generationBlockCellEmbedding rule depth 0
        (generationWordEdge rule depth (fun index => (Fin.init word index).1))).vertex
          (if (retainedComponentState rule marks (List.ofFn word)).sourceSelected then
            (rule.network.endpoint (word (Fin.last (depth + 1))).1).1
          else (rule.network.endpoint (word (Fin.last (depth + 1))).1).2) := by
  have endpoint_identity := (generationBlockCellEmbedding rule depth 0
    (generationWordEdge rule depth (fun index => (Fin.init word index).1))).endpoint
      (word (Fin.last (depth + 1))).1
  change (rule.generation (depth + 1)).network.endpoint
      (finProdFinEquiv (generationWordEdge rule depth (fun index => (Fin.init word index).1),
        (word (Fin.last (depth + 1))).1)) = _ at endpoint_identity
  unfold componentWordAnchor
  rw [generationWordEdge_bottom]
  split_ifs
  · exact congrArg Prod.fst endpoint_identity
  · exact congrArg Prod.snd endpoint_identity

/-- The next cylinder anchor belongs to the selected component of its
actual parent cell, with the original noncrossing configuration retained. -/
theorem componentWordAnchor_child_reachable (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (word : Fin (depth + 2) → (Fin rule.edges × Bool))
    (parent_live : retainedComponentState rule marks (List.ofFn (Fin.init word)) ≠ .inactive)
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive) :
    (rule.network.openGraph (marks (componentEdgeAddress (List.ofFn (Fin.init word)),
      (retainedComponentState rule marks (List.ofFn (Fin.init word))).massOpened))).Reachable
      (plantedVertex rule.network (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected)
      (if (retainedComponentState rule marks (List.ofFn word)).sourceSelected then
        (rule.network.endpoint (word (Fin.last (depth + 1))).1).1
      else (rule.network.endpoint (word (Fin.last (depth + 1))).1).2) := by
  have state_identity : retainedComponentState rule marks (List.ofFn word) =
      componentChildState (rule.network.orientedChildState
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).sourceSelected
        (retainedComponentState rule marks (List.ofFn (Fin.init word))).targetSelected
        (marks (componentEdgeAddress (List.ofFn (Fin.init word)),
          (retainedComponentState rule marks (List.ofFn (Fin.init word))).massOpened))
        (word (Fin.last (depth + 1))).1) (word (Fin.last (depth + 1))).2 := by
    rw [List.ofFn_succ', List.concat_eq_append, retainedComponentState_append_singleton]
    rfl
  apply (single_oriented_component_selected_iff rule.network _ _
    (retainedComponentState_ne_both rule marks _) parent_live (crossing _ _) _).mp
  rw [state_identity]
  exact componentChildState_selected_endpoint rule.network _ _ _ _ _ (by rwa [← state_identity])

theorem generationWordEdge_massOpened (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (word : Fin (depth + 1) → (Fin rule.edges × Bool))
    (live : retainedComponentStateFrom rule marks ancestor parent (List.ofFn word) ≠ .inactive) :
    markedGenerationConfiguration rule marks depth ancestor parent.massOpened
      (generationWordEdge rule depth (fun index => (word index).1)) =
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn word)).massOpened := by
  induction depth generalizing ancestor parent with
  | zero =>
    have child_live : componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (ancestor, parent.massOpened)) (word 0).1) (word 0).2 ≠ .inactive := by
      simpa only [List.ofFn_succ, List.ofFn_zero, retainedComponentStateFrom] using live
    simpa only [generationWordEdge, markedGenerationConfiguration, List.ofFn_succ, List.ofFn_zero,
      retainedComponentStateFrom] using
        (live_component_child_crossing_bit rule.network _ _ _ _ _ child_live).symm
  | succ depth induction_hypothesis =>
    have child_live := retainedComponentStateFrom_live_parent rule marks (ancestor ++ [(word 0).1])
      (componentChildState (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (ancestor, parent.massOpened)) (word 0).1) (word 0).2)
      (List.ofFn (fun index : Fin (depth + 1) => word index.succ)) (by
        simpa only [List.ofFn_succ, retainedComponentStateFrom] using live)
    rw [generationWordEdge, markedGenerationConfiguration_top_apply,
      ← live_component_child_crossing_bit rule.network _ _ _ _ _ child_live]
    simpa only [List.ofFn_succ, retainedComponentStateFrom] using
      induction_hypothesis (ancestor ++ [(word 0).1]) _ (fun index => word index.succ) (by
        simpa only [List.ofFn_succ, retainedComponentStateFrom] using live)

end
end IGSIII.Geometry
