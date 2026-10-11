import Universality.Percolation.StateRowIdentities

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def rootEdgeTouched (ω : Configuration edges) (edge : Fin edges) : Bool :=
  (R.openGraph ω).reachableDecide R.source (R.endpoint edge).1 ||
    (R.openGraph ω).reachableDecide R.source (R.endpoint edge).2

theorem reachable_opened_first_iff (ω : Configuration edges) (edge : Fin edges) :
    (R.openGraph (Function.update ω edge true)).Reachable R.source (R.endpoint edge).1 ↔
      (R.openGraph ω).Reachable R.source (R.endpoint edge).1 ∨
        (R.openGraph ω).Reachable R.source (R.endpoint edge).2 := by
  rw [R.reachable_update_true_iff]
  constructor
  · rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h, .refl _⟩)

theorem reachableDecide_opened_first (ω : Configuration edges) (edge : Fin edges) :
    (R.openGraph (Function.update ω edge true)).reachableDecide R.source (R.endpoint edge).1 =
      R.rootEdgeTouched ω edge := by
  apply Bool.eq_iff_iff.mpr
  simp only [rootEdgeTouched, Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true]
  exact R.reachable_opened_first_iff ω edge

theorem active_connected (ω : Configuration edges) (v : Fin vertices) :
    R.active .connected ω v = (R.openGraph ω).reachableDecide R.source v := by
  simp only [active, show (LiveState.connected == LiveState.both) = false from by decide,
    Bool.false_and, Bool.or_false]

theorem childState_connected_eq_single (ω : Configuration edges) (edge : Fin edges) :
    R.childState .connected ω edge = R.childState .single ω edge := by
  simp only [childState, active_connected, active_single]

theorem childState_opened_connected_iff (ω : Configuration edges) (edge : Fin edges) :
    R.childState .single (Function.update ω edge true) edge = some .connected ↔
      R.rootEdgeTouched ω edge = true := by
  have hopen : Function.update ω edge true edge = true := by simp
  have heq := R.active_endpoints_eq_of_open .single (Function.update ω edge true) edge hopen
  simp only [childState, ← heq, active_single, R.reachableDecide_opened_first,
    hopen]
  cases R.rootEdgeTouched ω edge <;> simp

theorem childState_closed_live_iff (ω : Configuration edges) (edge : Fin edges)
    (hclosed : ω edge = false) :
    (R.childState .single ω edge = some .both ∨ R.childState .single ω edge = some .single) ↔
      R.rootEdgeTouched ω edge = true := by
  simp only [childState, active_single, hclosed, rootEdgeTouched]
  cases (R.openGraph ω).reachableDecide R.source (R.endpoint edge).1 <;>
    cases (R.openGraph ω).reachableDecide R.source (R.endpoint edge).2 <;> simp

theorem pivotal_imp_touched_closed (ω : Configuration edges) (edge : Fin edges)
    (hpivotal : R.pivotal ω edge = true) :
    R.rootEdgeTouched (Function.update ω edge false) edge = true := by
  have hc : R.crosses (Function.update ω edge false) = false := by
    simpa only [pivotal, Bool.and_eq_true, Bool.not_eq_true'] using
      (show R.crosses (Function.update ω edge true) = true ∧
        R.crosses (Function.update ω edge false) = false from by
          simpa only [pivotal, Bool.and_eq_true, Bool.not_eq_true'] using hpivotal).2
  have hp : R.pivotal (Function.update ω edge false) edge = true := by
    simpa only [R.pivotal_update] using hpivotal
  have hbridge := (R.pivotal_of_disconnected_iff _ edge hc).mp hp
  simp only [rootEdgeTouched, Bool.or_eq_true, SimpleGraph.reachableDecide_eq_true]
  rcases hbridge with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

def connectedOpenEdgeIndicator (ω : Configuration edges) (edge : Fin edges) : ℝ :=
  if R.crosses ω then (if R.childState .connected ω edge = some .connected then 1 else 0) else 0

def connectedClosedEdgeIndicator (ω : Configuration edges) (edge : Fin edges) : ℝ :=
  if R.crosses ω then (if R.childState .connected ω edge = some .both ∨
    R.childState .connected ω edge = some .single then 1 else 0) else 0

def disconnectedOpenEdgeIndicator (ω : Configuration edges) (edge : Fin edges) : ℝ :=
  if R.crosses ω then 0 else (if R.childState .single ω edge = some .connected then 1 else 0)

def disconnectedClosedEdgeIndicator (ω : Configuration edges) (edge : Fin edges) : ℝ :=
  if R.crosses ω then 0 else (if R.childState .single ω edge = some .both ∨
    R.childState .single ω edge = some .single then 1 else 0)

theorem root_edge_pairing (ω : Configuration edges) (edge : Fin edges) :
    R.connectedOpenEdgeIndicator (Function.update ω edge true) edge -
      R.connectedClosedEdgeIndicator (Function.update ω edge false) edge =
        (if R.pivotal ω edge then 1 else 0) ∧
    R.disconnectedOpenEdgeIndicator (Function.update ω edge true) edge -
      R.disconnectedClosedEdgeIndicator (Function.update ω edge false) edge =
        -(if R.pivotal ω edge then 1 else 0) := by
  have hmonotone := R.crosses_update_false_le_true ω edge
  have htouched := R.pivotal_imp_touched_closed ω edge
  have hopen := R.childState_opened_connected_iff (Function.update ω edge false) edge
  simp only [Function.update_idem] at hopen
  have hclosed := R.childState_closed_live_iff (Function.update ω edge false) edge (by simp)
  simp only [connectedOpenEdgeIndicator, connectedClosedEdgeIndicator,
    disconnectedOpenEdgeIndicator, disconnectedClosedEdgeIndicator,
    childState_connected_eq_single, hopen, hclosed]
  cases ha : R.crosses (Function.update ω edge true) <;>
    cases hb : R.crosses (Function.update ω edge false) <;>
    cases hc : R.rootEdgeTouched (Function.update ω edge false) edge <;>
    simp_all [pivotal]

end
end Universality.FiniteNetwork
