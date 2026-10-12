import IGSIII4.SpectralDensity.ActualCrossing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def PathIntervalCut (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (left right : Fin (interior + 2)) : Vertex blocks paths interior → Prop
  | .inr (.inr (otherBlock, otherPath, position)) =>
      otherBlock = block ∧ otherPath = path ∧ left.val < position.val + 1 ∧ position.val + 1 ≤ right.val
  | _ => False

theorem pathIntervalCut_pathVertex {blocks paths interior : ℕ} (block : Fin blocks) (path : Fin paths)
    (left right : Fin (interior + 2)) (otherBlock : Fin blocks) (otherPath : Fin paths)
    (position : Fin (interior + 3)) :
    PathIntervalCut blocks paths interior block path left right
      (pathVertex blocks paths interior otherBlock otherPath position) ↔
      otherBlock = block ∧ otherPath = path ∧ left.val < position.val ∧ position.val ≤ right.val := by
  have positionBound := position.isLt
  have rightBound := right.isLt
  simp only [pathVertex]
  split_ifs with first last
  · simp [PathIntervalCut, first]
  · simp only [PathIntervalCut, false_iff]
    rintro ⟨_, _, _, comparison⟩
    omega
  · have identity : position.val - 1 + 1 = position.val := by omega
    simp only [PathIntervalCut, identity]

theorem pathIntervalCut_preserved {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (block : Fin blocks) (path : Fin paths)
    (left right : Fin (interior + 2))
    (leftClosed : configuration (.inr (block, path, left)) ≠ true)
    (rightClosed : configuration (.inr (block, path, right)) ≠ true) :
    ∀ edge, configuration edge = true →
      (PathIntervalCut blocks paths interior block path left right (endpoint blocks paths interior edge).1 ↔
        PathIntervalCut blocks paths interior block path left right (endpoint blocks paths interior edge).2) := by
  intro edge opened
  rcases edge with outer | ⟨otherBlock, otherPath, edge⟩
  · fin_cases outer <;> simp [endpoint, PathIntervalCut, source, midpoint, target]
  · simp only [endpoint, pathIntervalCut_pathVertex, Fin.val_castSucc, Fin.val_succ]
    by_cases sameBlock : otherBlock = block
    · subst otherBlock
      by_cases samePath : otherPath = path
      · subst otherPath
        have differentLeft : edge.val ≠ left.val := by
          intro equal
          have edgeEqual : edge = left := Fin.ext equal
          subst edge
          exact leftClosed opened
        have differentRight : edge.val ≠ right.val := by
          intro equal
          have edgeEqual : edge = right := Fin.ext equal
          subst edge
          exact rightClosed opened
        simp only [true_and]
        omega
      · simp [samePath]
    · simp [sameBlock]

/-- A terminal can enter an internally isolated path only through one of its junctions. -/
theorem terminal_reachable_pathVertex_prefix_or_suffix {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (terminal : Fin 3)
    (block : Fin blocks) (path : Fin paths) (position : Fin (interior + 3))
    (reachable : (graph blocks paths interior configuration).Reachable (.inl terminal)
      (pathVertex blocks paths interior block path position)) :
    (∀ edge : Fin (interior + 2), edge.val < position.val → configuration (.inr (block, path, edge)) = true) ∨
      (∀ edge : Fin (interior + 2), position.val ≤ edge.val → configuration (.inr (block, path, edge)) = true) := by
  by_contra failed
  push Not at failed
  rcases failed with ⟨leftFailure, rightFailure⟩
  obtain ⟨left, before, leftClosed⟩ := leftFailure
  obtain ⟨right, after, rightClosed⟩ := rightFailure
  have cut := reachable_cut configuration (PathIntervalCut blocks paths interior block path left right)
    (pathIntervalCut_preserved configuration block path left right leftClosed rightClosed) reachable
  have label : PathIntervalCut blocks paths interior block path left right
      (pathVertex blocks paths interior block path position) :=
    (pathIntervalCut_pathVertex block path left right block path position).mpr ⟨rfl, rfl, before, after⟩
  exact (show ¬PathIntervalCut blocks paths interior block path left right (.inl terminal) by simp [PathIntervalCut]) (cut.mpr label)

def EdgeEndEvent (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool)
    (block : Fin blocks) (path : Fin paths) (edge : Fin (interior + 2)) : Prop :=
  (∀ earlier : Fin (interior + 2), earlier.val < edge.val → configuration (.inr (block, path, earlier)) = true) ∨
    (∀ later : Fin (interior + 2), edge.val < later.val → configuration (.inr (block, path, later)) = true)

theorem terminal_reachable_endpoint_implies_end_event {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (terminal : Fin 3)
    (block : Fin blocks) (path : Fin paths) (edge : Fin (interior + 2))
    (reachable : (graph blocks paths interior configuration).Reachable (.inl terminal)
        (endpoint blocks paths interior (.inr (block, path, edge))).1 ∨
      (graph blocks paths interior configuration).Reachable (.inl terminal)
        (endpoint blocks paths interior (.inr (block, path, edge))).2) :
    EdgeEndEvent blocks paths interior configuration block path edge := by
  rcases reachable with first | second
  · have entry := terminal_reachable_pathVertex_prefix_or_suffix configuration terminal block path edge.castSucc first
    rcases entry with initialOpen | finalOpen
    · exact Or.inl initialOpen
    · exact Or.inr (fun later after => finalOpen later (by simp only [Fin.val_castSucc]; omega))
  · have entry := terminal_reachable_pathVertex_prefix_or_suffix configuration terminal block path edge.succ second
    rcases entry with initialOpen | finalOpen
    · exact Or.inl (fun earlier before => initialOpen earlier (by simp only [Fin.val_succ]; omega))
    · exact Or.inr (fun later after => finalOpen later (by simp only [Fin.val_succ]; omega))

end
end IGSIII4.SpectralDensity.ActualFamily
