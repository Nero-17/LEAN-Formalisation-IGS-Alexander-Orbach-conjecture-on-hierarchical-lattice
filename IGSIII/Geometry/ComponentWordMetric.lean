import IGSIII.Geometry.AddressMetricPersistence
import IGSIII.Chemical.SmallBall.ComponentOwnershipEmbedding

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem generationComponentWordEmbedding_restrict (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive) :
    (generationComponentWordEmbedding rule fine age (fun index => (word index).1)).restrict
      (markedGenerationConfiguration rule marks (fine + age) [] true) =
      markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened := by
  have address : componentEdgeAddress (List.ofFn word) = List.ofFn (fun index => (word index).1) := by
    simp only [componentEdgeAddress, List.map_ofFn, Function.comp_def]
  have identity := generationComponentWordEmbedding_address rule fine age (fun index => (word index).1)
  have restricted := eq_of_heq (dependentMap_heq
    (fun length (embedding : (rule.generation fine).network.NetworkEmbedding (rule.generation (fine + length)).network) =>
      embedding.restrict (markedGenerationConfiguration rule marks (fine + length) [] true))
    (show age = (List.ofFn (fun index => (word index).1)).length by simp) identity)
  rw [restricted, ← address]
  have original := generationAddressEmbedding_restrict_marked_component rule marks fine [] .connected (List.ofFn word) live
  change (generationAddressEmbedding rule (componentEdgeAddress (List.ofFn word)) fine).restrict
      (markedGenerationConfiguration rule marks (fine + (componentEdgeAddress (List.ofFn word)).length) [] true) =
      markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened at original
  exact original

theorem generationComponentWordEmbedding_planted (rule : Rule) (fine age : ℕ)
    (word : Fin (age + 1) → Fin rule.edges) (side : Bool) :
    (generationComponentWordEmbedding rule fine (age + 1) word).vertex
      (plantedVertex (rule.generation fine).network side) =
      persistentVertexEmbedding rule age (fine + age + 1) (by omega)
        (if side then ((rule.generation age).network.endpoint (generationWordEdge rule age word)).1
          else ((rule.generation age).network.endpoint (generationWordEdge rule age word)).2) := by
  induction age with
  | zero =>
      cases side with
      | false =>
        change (rule.generationCellEmbedding fine (word 0)).vertex (rule.generation fine).network.target =
          persistentVertexEmbedding rule 0 (fine + 1) (Nat.zero_le _) (rule.network.endpoint (word 0)).2
        rw [generationCellEmbedding_target, oldVertexEmbedding_eq_persistent]
      | true =>
        change (rule.generationCellEmbedding fine (word 0)).vertex (rule.generation fine).network.source =
          persistentVertexEmbedding rule 0 (fine + 1) (Nat.zero_le _) (rule.network.endpoint (word 0)).1
        rw [generationCellEmbedding_source, oldVertexEmbedding_eq_persistent]
  | succ age inductionHypothesis =>
      rw [generationComponentWordEmbedding]
      simp only [NetworkEmbedding.trans, Function.Embedding.trans_apply, Nat.add_succ, Nat.add_zero]
      have inherited := inductionHypothesis (fun index => word index.succ)
      simp only [Nat.add_succ, Nat.add_zero] at inherited
      rw [inherited]
      have commute := generationCellEmbedding_persistent rule age (fine + age + 1) (by omega) (word 0)
        (if side then ((rule.generation age).network.endpoint (generationWordEdge rule age (fun index => word index.succ))).1
          else ((rule.generation age).network.endpoint (generationWordEdge rule age (fun index => word index.succ))).2)
      simp only [Nat.add_succ, Nat.add_zero] at commute
      rw [← commute]
      congr 1
      have endpoints := (rule.generationCellEmbedding age (word 0)).endpoint
        (generationWordEdge rule age (fun index => word index.succ))
      change (rule.generation (age + 1)).network.endpoint (generationWordEdge rule (age + 1) word) = _ at endpoints
      cases side with
      | false => exact (congrArg Prod.snd endpoints).symm
      | true => exact (congrArg Prod.fst endpoints).symm

theorem generationComponentWordEmbedding_distance_to_planted_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (fine age : ℕ) (word : Fin age → (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive)
    (vertex : Fin (rule.generation fine).vertices)
    (reachable : ((rule.generation fine).network.openGraph
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened)).Reachable
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected) vertex) :
    ((rule.generation (fine + age)).network.openGraph (markedGenerationConfiguration rule marks (fine + age) [] true)).dist
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).vertex
        (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected))
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).vertex vertex) ≤
      terminalComponentRadius (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
          (retainedComponentState rule marks (List.ofFn word)).massOpened) := by
  have restriction := generationComponentWordEmbedding_restrict rule marks fine age word live
  have restrictedReachable : ((rule.generation fine).network.openGraph
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).restrict
        (markedGenerationConfiguration rule marks (fine + age) [] true))).Reachable
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected) vertex := by
    rw [restriction]
    exact reachable
  obtain ⟨walk, length⟩ := restrictedReachable.exists_walk_length_eq_dist
  have estimate := SimpleGraph.dist_le (walk.map
    ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).openGraphHom
      (markedGenerationConfiguration rule marks (fine + age) [] true)))
  simp only [SimpleGraph.Walk.length_map, length] at estimate
  change ((rule.generation (fine + age)).network.openGraph (markedGenerationConfiguration rule marks (fine + age) [] true)).dist
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).vertex _)
      ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).vertex vertex) ≤
      ((rule.generation fine).network.openGraph
        ((generationComponentWordEmbedding rule fine age (fun index => (word index).1)).restrict
          (markedGenerationConfiguration rule marks (fine + age) [] true))).dist _ vertex at estimate
  rw [restriction] at estimate
  have radiusBound (side : Bool) : ((rule.generation fine).network.openGraph
      (markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
        (retainedComponentState rule marks (List.ofFn word)).massOpened)).dist
      (plantedVertex (rule.generation fine).network side) vertex ≤
      terminalComponentRadius (rule.generation fine).network
        (markedGenerationConfiguration rule marks fine (componentEdgeAddress (List.ofFn word))
          (retainedComponentState rule marks (List.ofFn word)).massOpened) := by
    cases side with
    | false => exact target_distance_le_terminalComponentRadius _ _ vertex
    | true => exact source_distance_le_terminalComponentRadius _ _ vertex
  exact estimate.trans (radiusBound _)

end
end IGSIII.Geometry
