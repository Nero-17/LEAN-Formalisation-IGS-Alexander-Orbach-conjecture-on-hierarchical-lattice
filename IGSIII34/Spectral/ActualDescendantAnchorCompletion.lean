import IGSIII34.ResistanceLimit.ActualCutoffFlatnessCompletion
import IGSIII.Geometry.ComponentWordAnchors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit Resistance
open MeasureTheory Filter
open scoped BigOperators Topology

def blockWordAppendCompletion {Entry : Type*} (coarse fine : ℕ)
    (parentWord : Fin (coarse + 1) → Entry) (suffix : Fin (fine + 1) → Entry) :
    Fin (coarse + fine + 2) → Entry :=
  fun index => Fin.append parentWord suffix (Fin.cast (by omega) index)

theorem block_word_append_ofFn_completion {Entry : Type*} (coarse fine : ℕ)
    (parentWord : Fin (coarse + 1) → Entry) (suffix : Fin (fine + 1) → Entry) :
    List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix) =
      List.ofFn parentWord ++ List.ofFn suffix := by
  exact (List.ofFn_congr (by omega : (coarse + 1) + (fine + 1) = coarse + fine + 2)
    (Fin.append parentWord suffix)).symm.trans (List.ofFn_fin_append parentWord suffix)

theorem generation_word_edge_append_completion
    (rule : Rule) (coarse fine : ℕ)
    (parentWord : Fin (coarse + 1) → Fin rule.edges) (suffix : Fin (fine + 1) → Fin rule.edges) :
    generationWordEdge rule (coarse + fine + 1) (blockWordAppendCompletion coarse fine parentWord suffix) =
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse parentWord)).edge
        (generationWordEdge rule fine suffix) := by
  apply generationEdgeAddress_injective rule (coarse + fine + 1)
  rw [generationWordEdge_address]
  change List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix) =
    generationEdgeAddress rule (coarse + fine + 1)
      ((rule.generationBlockDecomposition coarse fine).edge.symm
        (finProdFinEquiv (generationWordEdge rule coarse parentWord, generationWordEdge rule fine suffix)))
  rw [generationEdgeAddress_block, generationWordEdge_address, generationWordEdge_address, block_word_append_ofFn_completion]

theorem component_descendant_anchor_block_identity_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse fine : ℕ) (parentWord : Fin (coarse + 1) → (Fin rule.edges × Bool))
    (suffix : Fin (fine + 1) → (Fin rule.edges × Bool)) :
    componentWordAnchor rule marks (coarse + fine + 1) (blockWordAppendCompletion coarse fine parentWord suffix) =
      (generationBlockCellEmbedding rule coarse fine
        (generationWordEdge rule coarse (fun index => (parentWord index).1))).vertex
          (if (retainedComponentState rule marks (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix))).sourceSelected then
            ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).1
          else ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).2) := by
  have firstCoordinates : (fun index => (blockWordAppendCompletion coarse fine parentWord suffix index).1) =
      blockWordAppendCompletion coarse fine (fun index => (parentWord index).1) (fun index => (suffix index).1) := by
    have mapped (index : Fin ((coarse + 1) + (fine + 1))) :
        (Fin.append parentWord suffix index).1 =
          Fin.append (fun index => (parentWord index).1) (fun index => (suffix index).1) index := by
      refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;> simp
    funext index
    exact mapped (Fin.cast (by omega) index)
  unfold componentWordAnchor
  rw [firstCoordinates, generation_word_edge_append_completion]
  rw [(generationBlockCellEmbedding rule coarse fine
    (generationWordEdge rule coarse (fun index => (parentWord index).1))).endpoint]
  split_ifs <;> rfl

/-- A descendant anchor belongs to the actual selected parent component
before any completion, including either retained side of a noncrossing cell. -/
theorem selected_word_anchor_local_reachable_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fine : ℕ) (ancestor : List (Fin rule.edges)) (parent : OrientedState)
    (notBoth : parent ≠ .both) (parentLive : parent ≠ .inactive)
    (suffix : Fin (fine + 1) → (Fin rule.edges × Bool))
    (live : retainedComponentStateFrom rule marks ancestor parent (List.ofFn suffix) ≠ .inactive) :
    ((rule.generation fine).network.openGraph (markedGenerationConfiguration rule marks fine ancestor parent.massOpened)).Reachable
      (plantedVertex (rule.generation fine).network parent.sourceSelected)
      (if (retainedComponentStateFrom rule marks ancestor parent (List.ofFn suffix)).sourceSelected then
        ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).1
      else ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).2) := by
  have finalNotBoth := retainedComponentStateFrom_ne_both rule marks ancestor parent notBoth (List.ofFn suffix)
  have selected : rule.network.selectedActive
      (retainedComponentStateFrom rule marks ancestor parent (List.ofFn suffix)).sourceSelected
      (retainedComponentStateFrom rule marks ancestor parent (List.ofFn suffix)).targetSelected
      (marks (ancestor ++ componentEdgeAddress (List.ofFn suffix),
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn suffix)).massOpened))
      (plantedVertex rule.network
        (retainedComponentStateFrom rule marks ancestor parent (List.ofFn suffix)).sourceSelected) = true := by
    apply (single_oriented_component_selected_iff rule.network _ _ finalNotBoth live (crossing _ _) _).mpr
    exact SimpleGraph.Reachable.refl _
  have inherited := generationWordVertexEmbedding_selected_component rule marks crossing fine ancestor parent suffix live _ selected
  have retained := (single_oriented_component_selected_iff (rule.generation (fine + 1)).network _ parent
    notBoth parentLive (markedGenerationConfiguration_crosses rule marks crossing (fine + 1) ancestor parent.massOpened) _).mp inherited
  rw [generationAddressEmbedding_word_planted] at retained
  have plantedIdentity := generationOldVertex_planted rule fine parent.sourceSelected
  rw [← plantedIdentity, rule.generation_reachable_old_iff,
    markedGenerationConfiguration_coarsens rule marks crossing fine ancestor parent.massOpened] at retained
  exact retained

theorem actual_component_descendant_anchor_local_reachable_completion
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coarse fine : ℕ) (parentWord : Fin (coarse + 1) → (Fin rule.edges × Bool))
    (suffix : Fin (fine + 1) → (Fin rule.edges × Bool))
    (prefixLive : retainedComponentState rule marks (List.ofFn parentWord) ≠ .inactive)
    (live : retainedComponentState rule marks (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix)) ≠ .inactive) :
    ((rule.generation fine).network.openGraph
      (generationBlockCells rule coarse fine (stationaryConfiguration rule marks (coarse + fine + 1))
        (generationWordEdge rule coarse (fun index => (parentWord index).1)))).Reachable
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn parentWord)).sourceSelected)
      (if (retainedComponentState rule marks (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix))).sourceSelected then
        ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).1
      else ((rule.generation fine).network.endpoint (generationWordEdge rule fine (fun index => (suffix index).1))).2) := by
  have stateIdentity : retainedComponentStateFrom rule marks (componentEdgeAddress (List.ofFn parentWord))
      (retainedComponentState rule marks (List.ofFn parentWord)) (List.ofFn suffix) =
        retainedComponentState rule marks (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix)) := by
    simp only [block_word_append_ofFn_completion, retainedComponentState,
      retainedComponentStateFrom_append, List.nil_append]
  have localReach := selected_word_anchor_local_reachable_completion rule marks crossing fine
    (componentEdgeAddress (List.ofFn parentWord)) (retainedComponentState rule marks (List.ofFn parentWord))
    (retainedComponentState_ne_both rule marks _) prefixLive suffix (by rwa [stateIdentity])
  rw [stateIdentity] at localReach
  rw [stationaryConfiguration, generationBlockCells_marked, List.nil_append,
    generationWordEdge_address]
  have bitIdentity := generationWordEdge_massOpened rule marks coarse [] .connected parentWord prefixLive
  change markedGenerationConfiguration rule marks coarse [] true
    (generationWordEdge rule coarse (fun index => (parentWord index).1)) =
      (retainedComponentState rule marks (List.ofFn parentWord)).massOpened at bitIdentity
  rw [bitIdentity]
  simpa only [componentEdgeAddress, List.map_ofFn, Function.comp_def] using localReach

end
end IGSIII34.Spectral


