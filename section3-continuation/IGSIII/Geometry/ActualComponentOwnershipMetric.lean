import IGSIII.Geometry.ActualFullComponentOwnership
import IGSIII.Geometry.ActualComponentRetainedAnchors
import IGSIII.Geometry.ComponentWordMetric

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

/-- The genuine component ownership moves every non-frontier vertex by no
more than its original descendant component radius, to its persistent
selected coarse endpoint. -/
theorem actualComponentVertexOwnership_distance_le
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale) (fine age : ℕ)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool))
    (point : ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + (age + 1)))
    (nonfrontier : point ∉ actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1)) :
    dist point (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive age (fine + (age + 1)) (by omega)
      (actualComponentRetainedAnchor rule marks crossing age
        (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point))) ≤
      (markedTerminalComponentRadius rule marks fine
        (componentEdgeAddress (List.ofFn (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point)))
        (retainedComponentState rule marks (List.ofFn (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point))).massOpened : ℝ) /
          scale ^ (fine + (age + 1) + 1) := by
  obtain ⟨child, childIdentity⟩ := actualComponentVertexOwnership_nonfrontier
    rule marks crossing scale scalePositive fine (age + 1) fallback point nonfrontier
  let word := actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point
  have live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive :=
    selectedComponentInterior_live rule marks fine _ _ child
  have reachable := (marked_component_selected_iff rule marks crossing fine (List.ofFn word) live child.val.val).mp child.property
  have distanceBound := generationComponentWordEmbedding_distance_to_planted_le rule marks fine (age + 1) word live child.val.val reachable
  have rawIdentity : point.val =
      (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex child.val.val := by
    have equality := congrArg (fun vertex : ActualFiniteCluster rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive (fine + (age + 1)) => vertex.val) childIdentity
    change (selectedComponentWordEmbedding rule marks crossing fine (age + 1) [] .connected ⟨word, child⟩).val.val = point.val at equality
    rw [selectedComponentWordEmbedding_vertex] at equality
    exact equality.symm
  have plantedIdentity := generationComponentWordEmbedding_planted rule fine age
    (fun index => (word index).1) (retainedComponentState rule marks (List.ofFn word)).sourceSelected
  change (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
      (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected) =
      persistentVertexEmbedding rule age (fine + age + 1) (by omega) (componentWordAnchor rule marks age word) at plantedIdentity
  change (((rule.generation (fine + (age + 1))).network.openGraph
      (markedGenerationConfiguration rule marks (fine + (age + 1)) [] true)).dist point.val
      (persistentVertexEmbedding rule age (fine + (age + 1)) (by omega)
        (actualComponentRetainedAnchor rule marks crossing age word).val) : ℝ) / scale ^ (fine + (age + 1) + 1) ≤ _
  simp only [actualComponentRetainedAnchor, dif_pos live]
  rw [rawIdentity, SimpleGraph.dist_comm]
  have normalized := div_le_div_of_nonneg_right (show
      (((rule.generation (fine + (age + 1))).network.openGraph
        (markedGenerationConfiguration rule marks (fine + (age + 1)) [] true)).dist
        ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex
          (plantedVertex (rule.generation fine).network (retainedComponentState rule marks (List.ofFn word)).sourceSelected))
        ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex child.val.val) : ℝ) ≤
        markedTerminalComponentRadius rule marks fine (componentEdgeAddress (List.ofFn word))
          (retainedComponentState rule marks (List.ofFn word)).massOpened by exact_mod_cast distanceBound)
    (pow_pos scalePositive (fine + (age + 1) + 1)).le
  rw [plantedIdentity] at normalized
  exact normalized

theorem actualComponentVertexOwnership_mesh_bound
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
    (scale : ℝ) (scalePositive : 0 < scale) (eta coefficient : ℝ) (start : ℕ)
    (radiusBound : ∀ address opened fine, start ≤ address.length →
      (markedTerminalComponentRadius rule marks fine address opened : ℝ) / scale ^ (fine + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (fine age : ℕ) (beyond : start ≤ age + 1)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool))
    (point : ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      scale scalePositive (fine + (age + 1)))
    (nonfrontier : point ∉ actualComponentVertexFrontier rule marks crossing scale scalePositive fine (age + 1)) :
    dist point (retainedFiniteVertexEmbedding rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
      coherent scale scalePositive age (fine + (age + 1)) (by omega)
      (actualComponentRetainedAnchor rule marks crossing age
        (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point))) ≤
      coefficient * eta ^ (age + 1) := by
  apply (actualComponentVertexOwnership_distance_le rule marks crossing coherent scale scalePositive fine age fallback point nonfrontier).trans
  have bound := radiusBound
    (componentEdgeAddress (List.ofFn (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point)))
    (retainedComponentState rule marks (List.ofFn (actualComponentVertexOwnership rule marks crossing scale scalePositive fine (age + 1) fallback point))).massOpened fine
    (by simpa only [componentEdgeAddress, List.length_map, List.length_ofFn] using beyond)
  simpa only [componentEdgeAddress, List.length_map, List.length_ofFn, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using bound

end
end IGSIII.Geometry
