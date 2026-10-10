import IGSIII.Mass.HistoryPathLaw
import Universality.Percolation.MassEquivalence

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

def OrientedState.massOpened (parent : OrientedState) : Bool := decide (parent = .connected)

end Universality.FiniteNetwork

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open scoped BigOperators

/-- Actual internal retained-component count at an address, using its original
crossing or noncrossing mark and only changing the terminal mask. -/
noncomputable def markedOrientedVertexMass (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) : ℝ :=
  ((rule.generation depth).network.internalStateMass parent
    (markedGenerationConfiguration rule marks depth address parent.massOpened) : ℝ)

theorem markedOrientedVertexMass_inactive (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    markedOrientedVertexMass rule marks depth address .inactive = 0 := by
  simp [markedOrientedVertexMass, internalStateMass_inactive]

theorem markedOrientedVertexMass_joint_both (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    markedOrientedVertexMass rule marks depth address .both =
      markedOrientedVertexMass rule marks depth address .sourceOnly +
        markedOrientedVertexMass rule marks depth address .targetOnly := by
  have disconnected := markedGenerationConfiguration_crosses rule marks crossing depth address false
  simpa [markedOrientedVertexMass, internalStateMass, OrientedState.sourceSelected,
    OrientedState.targetSelected, OrientedState.massOpened, Nat.cast_add] using
      congrArg (fun count : ℕ => (count : ℝ))
        ((rule.generation depth).network.internalSelectedMass_disconnected _ disconnected)

/-- Exact finite-depth birth-cell decomposition for every retained mask.
The B sides use the same noncrossing marks throughout the identity. -/
theorem markedOrientedVertexMass_substitute (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) (parent : OrientedState) :
    markedOrientedVertexMass rule marks (depth + 1) address parent =
      (rule.network.internalStateMass parent (marks (address, parent.massOpened)) : ℝ) +
      ∑ edge, markedOrientedVertexMass rule marks depth (address ++ [edge])
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge) := by
  have coarse : (rule.generation depth).network.coarseConfiguration
      (fun edge => markedGenerationConfiguration rule marks depth (address ++ [edge])
        (marks (address, parent.massOpened) edge)) = marks (address, parent.massOpened) := by
    funext edge
    exact markedGenerationConfiguration_crosses rule marks crossing depth _ _
  have finite_identity :
      (rule.generation (depth + 1)).network.internalStateMass parent
        (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened) =
      rule.network.internalStateMass parent (marks (address, parent.massOpened)) +
      ∑ edge, (rule.generation depth).network.internalStateMass
        (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge)
        (markedGenerationConfiguration rule marks depth (address ++ [edge])
          (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
            (marks (address, parent.massOpened)) edge).massOpened) := by
    change (rule.generation (depth + 1)).network.internalSelectedMass parent.sourceSelected parent.targetSelected
      (markedGenerationConfiguration rule marks (depth + 1) address parent.massOpened) =
        rule.network.internalSelectedMass parent.sourceSelected parent.targetSelected (marks (address, parent.massOpened)) + _
    rw [← (rule.generationTopDecomposition depth).internalSelectedMass,
      ← configuration_of_topCells, markedGenerationConfiguration_topCells,
      rule.network.internalSelectedMass_substitute, coarse]
    congr 1
    apply Finset.sum_congr rfl
    intro edge _
    by_cases inactive : rule.network.orientedChildState parent.sourceSelected parent.targetSelected
        (marks (address, parent.massOpened)) edge = .inactive
    · simp only [inactive, internalStateMass_inactive]
    · have bit : (rule.network.orientedChildState parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge).massOpened = marks (address, parent.massOpened) edge := by
        apply Bool.eq_iff_iff.mpr
        simp only [OrientedState.massOpened, decide_eq_true_eq]
        exact rule.network.live_oriented_state_determines_crossing parent.sourceSelected parent.targetSelected
          (marks (address, parent.massOpened)) edge inactive
      rw [bit]
  simpa only [markedOrientedVertexMass, Nat.cast_add, Nat.cast_sum] using
    congrArg (fun count : ℕ => (count : ℝ)) finite_identity

end IGSIII.Chemical.Substitution
