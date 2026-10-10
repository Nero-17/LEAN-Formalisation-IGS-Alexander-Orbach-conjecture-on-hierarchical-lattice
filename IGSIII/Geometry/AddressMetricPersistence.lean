import IGSIII.Geometry.ActualAddressEmbedding
import IGSIII.Geometry.ActualSkeletonPersistence
import IGSIII.Geometry.ComponentWordAnchors

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem oldVertexEmbedding_eq_persistent (rule : Rule) (depth : ℕ) (vertex : Fin rule.vertices) :
    oldVertexEmbedding rule depth vertex = persistentVertexEmbedding rule 0 (depth + 1) (Nat.zero_le _) vertex := by
  induction depth with
  | zero => rfl
  | succ depth induction_hypothesis =>
      rw [← oldVertexEmbedding_next, induction_hypothesis]
      change rule.generationOldVertex (depth + 1)
        (Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices) (show 0 ≤ depth + 1 by omega)
          (fun {depth} => rule.generationOldVertex depth) vertex) =
        Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices) (show 0 ≤ (depth + 1) + 1 by omega)
          (fun {depth} => rule.generationOldVertex depth) vertex
      rw [Nat.leRecOn_succ (show 0 ≤ depth + 1 by omega)]

theorem generationCellEmbedding_persistent (rule : Rule) (first second : ℕ) (bound : first ≤ second)
    (edge : Fin rule.edges) (vertex : Fin (rule.generation first).vertices) :
    persistentVertexEmbedding rule (first + 1) (second + 1) (by omega)
      ((rule.generationCellEmbedding first edge).vertex vertex) =
      (rule.generationCellEmbedding second edge).vertex (persistentVertexEmbedding rule first second bound vertex) := by
  induction second, bound using Nat.le_induction with
  | base =>
    simp only [persistentVertexEmbedding, Universality.Geometry.IsometricSequence.transition,
      Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ second bound induction_hypothesis =>
    change Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
      (show first + 1 ≤ (second + 1) + 1 by omega) (fun {depth} => rule.generationOldVertex depth)
      ((rule.generationCellEmbedding first edge).vertex vertex) =
      (rule.generationCellEmbedding (second + 1) edge).vertex
        (Nat.leRecOn (C := fun depth => Fin (rule.generation depth).vertices)
          (show first ≤ second + 1 by omega) (fun {depth} => rule.generationOldVertex depth) vertex)
    rw [Nat.leRecOn_succ (show first + 1 ≤ second + 1 by omega), Nat.leRecOn_succ bound]
    change rule.generationOldVertex (second + 1)
      (persistentVertexEmbedding rule (first + 1) (second + 1) (by omega)
        ((rule.generationCellEmbedding first edge).vertex vertex)) = _
    rw [induction_hypothesis, rule.generationCellEmbedding_oldVertex]
    rfl

theorem generationAddressEmbedding_persistent (rule : Rule) (address : List (Fin rule.edges))
    (first second : ℕ) (bound : first ≤ second) (vertex : Fin (rule.generation first).vertices) :
    persistentVertexEmbedding rule (first + address.length) (second + address.length) (by omega)
      ((generationAddressEmbedding rule address first).vertex vertex) =
      (generationAddressEmbedding rule address second).vertex (persistentVertexEmbedding rule first second bound vertex) := by
  induction address with
  | nil => rfl
  | cons edge tail induction_hypothesis =>
    simp only [generationAddressEmbedding, List.length_cons, Nat.add_succ,
      id_eq, NetworkEmbedding.trans, Function.Embedding.trans_apply]
    rw [generationCellEmbedding_persistent rule (first + tail.length) (second + tail.length) (by omega) edge _,
      induction_hypothesis]

theorem generationAddressEmbedding_distance_to_planted_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges × Bool))
    (live : retainedComponentState rule marks address ≠ .inactive)
    (vertex : Fin (rule.generation depth).vertices)
    (reachable : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (componentEdgeAddress address)
        (retainedComponentState rule marks address).massOpened)).Reachable
        (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected) vertex) :
    ((rule.generation (depth + (componentEdgeAddress address).length)).network.openGraph
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) [] true)).dist
      ((generationAddressEmbedding rule (componentEdgeAddress address) depth).vertex
        (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected))
      ((generationAddressEmbedding rule (componentEdgeAddress address) depth).vertex vertex) ≤
      terminalComponentRadius (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth (componentEdgeAddress address)
          (retainedComponentState rule marks address).massOpened) := by
  have restriction := generationAddressEmbedding_restrict_marked_component rule marks depth [] .connected address live
  change (generationAddressEmbedding rule (componentEdgeAddress address) depth).restrict
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) [] true) =
    markedGenerationConfiguration rule marks depth (componentEdgeAddress address)
      (retainedComponentState rule marks address).massOpened at restriction
  have restricted_reachable : (((generationAddressEmbedding rule (componentEdgeAddress address) depth).restrict
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) [] true))
      |> (rule.generation depth).network.openGraph).Reachable
      (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected) vertex := by
    rw [restriction]
    exact reachable
  obtain ⟨walk, length⟩ := restricted_reachable.exists_walk_length_eq_dist
  have estimate := SimpleGraph.dist_le (walk.map
    ((generationAddressEmbedding rule (componentEdgeAddress address) depth).openGraphHom
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) [] true)))
  simp only [SimpleGraph.Walk.length_map, length] at estimate
  change ((rule.generation (depth + (componentEdgeAddress address).length)).network.openGraph
    (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) [] true)).dist
    ((generationAddressEmbedding rule (componentEdgeAddress address) depth).vertex
      (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected))
    ((generationAddressEmbedding rule (componentEdgeAddress address) depth).vertex vertex) ≤
    ((rule.generation depth).network.openGraph ((generationAddressEmbedding rule (componentEdgeAddress address) depth).restrict
      (markedGenerationConfiguration rule marks (depth + (componentEdgeAddress address).length) [] true))).dist
      (plantedVertex (rule.generation depth).network (retainedComponentState rule marks address).sourceSelected) vertex at estimate
  rw [restriction] at estimate
  have radius_bound (side : Bool) : ((rule.generation depth).network.openGraph
      (markedGenerationConfiguration rule marks depth (componentEdgeAddress address)
        (retainedComponentState rule marks address).massOpened)).dist
      (plantedVertex (rule.generation depth).network side) vertex ≤
      terminalComponentRadius (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth (componentEdgeAddress address)
          (retainedComponentState rule marks address).massOpened) := by
    cases side with
    | false => exact target_distance_le_terminalComponentRadius _ _ vertex
    | true => exact source_distance_le_terminalComponentRadius _ _ vertex
  exact estimate.trans (radius_bound (retainedComponentState rule marks address).sourceSelected)

end
end IGSIII.Geometry
