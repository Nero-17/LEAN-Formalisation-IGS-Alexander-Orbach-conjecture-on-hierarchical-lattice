import IGSIII34.Spectral.Collars.FiniteOwnerComparison
import IGSIII34.Spectral.ActualDescendantAnchorCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 180000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter
open scoped Topology

theorem single_oriented_state_eq_of_side_and_crossing
    (first last : OrientedState) (firstLive : first ≠ .inactive) (lastLive : last ≠ .inactive)
    (firstSingle : first ≠ .both) (lastSingle : last ≠ .both)
    (side : first.sourceSelected = last.sourceSelected)
    (crossing : first.massOpened = last.massOpened) : first = last := by
  cases first <;> cases last <;>
    simp_all [OrientedState.sourceSelected, OrientedState.massOpened]

/-- A positive actual prefix cannot duplicate another positive label of
the same physical socket and selected component. This follows from the
injective ownership of actual interior vertices at a finite generation. -/
theorem actual_positive_component_words_unique_slot
    (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (first last : Fin (depth + 1) → (Fin rule.edges × Bool))
    (weight : List (Fin rule.edges × Bool) → ℝ)
    (actualRatios : ∀ address, Tendsto (fun fine =>
      markedOrientedVertexMass rule marks fine (componentEdgeAddress address)
        (retainedComponentState rule marks address) /
        markedOrientedVertexMass rule marks (fine + address.length) [] .connected)
      atTop (𝓝 (weight address)))
    (firstPositive : 0 < weight (List.ofFn first))
    (firstLive : retainedComponentState rule marks (List.ofFn first) ≠ .inactive)
    (lastLive : retainedComponentState rule marks (List.ofFn last) ≠ .inactive)
    (sameEdges : (fun index => (first index).1) = fun index => (last index).1)
    (sameSide : (retainedComponentState rule marks (List.ofFn first)).sourceSelected =
      (retainedComponentState rule marks (List.ofFn last)).sourceSelected) : first = last := by
  classical
  have sameAddress : componentEdgeAddress (List.ofFn first) = componentEdgeAddress (List.ofFn last) := by
    simpa only [componentEdgeAddress, List.map_ofFn, Function.comp_def] using congrArg List.ofFn sameEdges
  have firstBit := generationWordEdge_massOpened rule marks depth [] .connected first firstLive
  have lastBit := generationWordEdge_massOpened rule marks depth [] .connected last lastLive
  change markedGenerationConfiguration rule marks depth [] true
    (generationWordEdge rule depth (fun index => (first index).1)) =
      (retainedComponentState rule marks (List.ofFn first)).massOpened at firstBit
  change markedGenerationConfiguration rule marks depth [] true
    (generationWordEdge rule depth (fun index => (last index).1)) =
      (retainedComponentState rule marks (List.ofFn last)).massOpened at lastBit
  have sameCrossing : (retainedComponentState rule marks (List.ofFn first)).massOpened =
      (retainedComponentState rule marks (List.ofFn last)).massOpened := by
    rw [← firstBit, ← lastBit, sameEdges]
  have sameState := single_oriented_state_eq_of_side_and_crossing _ _ firstLive lastLive
    (retainedComponentState_ne_both rule marks _) (retainedComponentState_ne_both rule marks _)
    sameSide sameCrossing
  obtain ⟨fine, positiveRatio⟩ := ((actualRatios (List.ofFn first)).eventually (lt_mem_nhds firstPositive)).exists
  have numeratorPositive : 0 < markedOrientedVertexMass rule marks fine
      (componentEdgeAddress (List.ofFn first)) (retainedComponentState rule marks (List.ofFn first)) := by
    by_contra notPositive
    have nonpositive := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt notPositive)
      (show 0 ≤ markedOrientedVertexMass rule marks (fine + (List.ofFn first).length) [] .connected from
        Nat.cast_nonneg _)
    exact (not_lt_of_ge nonpositive) positiveRatio
  have nonempty : Nonempty (SelectedComponentInterior rule marks fine
      (componentEdgeAddress (List.ofFn first)) (retainedComponentState rule marks (List.ofFn first))) := by
    apply Fintype.card_pos_iff.mp
    have cardPositive := numeratorPositive
    rw [← selectedComponentInterior_card rule marks fine
      (componentEdgeAddress (List.ofFn first)) (retainedComponentState rule marks (List.ofFn first))] at cardPositive
    exact_mod_cast cardPositive
  obtain ⟨vertex⟩ := nonempty
  exact component_words_eq_of_common_finite_interior rule marks crossing fine (depth + 1)
    first last sameEdges sameState vertex

end
end IGSIII34.Spectral
