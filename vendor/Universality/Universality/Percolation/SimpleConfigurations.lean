import Universality.Graph.EdgeOpening
import Universality.Percolation.ClusterMass
import Universality.Percolation.StateRowIdentities

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem openGraph_all_closed : R.openGraph (fun _ => false) = ⊥ := by
  ext u v
  simp [openGraph]

theorem reachableDecide_all_closed (u v : Fin vertices) :
    (R.openGraph (fun _ => false)).reachableDecide u v = decide (u = v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [SimpleGraph.reachableDecide_eq_true, decide_eq_true_eq,
    R.openGraph_all_closed, SimpleGraph.reachable_bot]

theorem crosses_all_closed : R.crosses (fun _ => false) = false := by
  unfold crosses
  rw [reachableDecide_all_closed]
  simp [R.terminals_distinct]

theorem active_root (σ : LiveState) (ω : Configuration edges) :
    R.active σ ω R.source = true := by
  have hr : (R.openGraph ω).reachableDecide R.source R.source = true :=
    (SimpleGraph.reachableDecide_eq_true _ _ _).mpr (.refl _)
  simp [active, hr]

def onlyOpen (edge : Fin edges) : Configuration edges :=
  Function.update (fun _ => false) edge true

def onlyClosed (edge : Fin edges) : Configuration edges :=
  Function.update (fun _ => true) edge false

theorem reachable_onlyOpen_iff (edge : Fin edges) (u v : Fin vertices) :
    (R.openGraph (onlyOpen edge)).Reachable u v ↔
      u = v ∨ (u = (R.endpoint edge).1 ∧ (R.endpoint edge).2 = v) ∨
        (u = (R.endpoint edge).2 ∧ (R.endpoint edge).1 = v) := by
  rw [onlyOpen, R.reachable_update_true_iff]
  simp only [reachableAfterOpening, R.openGraph_all_closed, SimpleGraph.reachable_bot]

theorem crosses_onlyOpen_false (edge : Fin edges)
    (hfirst : (R.endpoint edge).1 ≠ R.target) (hsecond : (R.endpoint edge).2 ≠ R.target) :
    R.crosses (onlyOpen edge) = false := by
  apply Bool.eq_false_iff.mpr
  intro hcross
  have hreach := (R.crosses_eq_true _).mp hcross
  rw [reachable_onlyOpen_iff] at hreach
  simpa [R.terminals_distinct, hfirst, hsecond] using hreach

theorem active_at_incident_edge (σ : LiveState) (ω : Configuration edges) (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source) :
    R.active σ ω (R.endpoint edge).1 = true ∨ R.active σ ω (R.endpoint edge).2 = true := by
  rcases hincident with h | h
  · exact Or.inl (h ▸ R.active_root σ ω)
  · exact Or.inr (h ▸ R.active_root σ ω)

theorem childState_onlyOpen (σ : LiveState) (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source) :
    R.childState σ (onlyOpen edge) edge = some .connected := by
  have hopen : onlyOpen edge edge = true := by simp [onlyOpen]
  have heq := R.active_endpoints_eq_of_open σ (onlyOpen edge) edge hopen
  have ha : R.active σ (onlyOpen edge) (R.endpoint edge).1 = true := by
    rcases R.active_at_incident_edge σ (onlyOpen edge) edge hincident with h | h
    · exact h
    · exact heq.trans h
  exact (R.childState_connected_iff σ (onlyOpen edge) edge).mpr ⟨hopen, ha⟩

theorem childState_allOpen (σ : LiveState) (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source) :
    R.childState σ (fun _ => true) edge = some .connected := by
  have heq := R.active_endpoints_eq_of_open σ (fun _ => true) edge rfl
  have ha : R.active σ (fun _ => true) (R.endpoint edge).1 = true := by
    rcases R.active_at_incident_edge σ (fun _ => true) edge hincident with h | h
    · exact h
    · exact heq.trans h
  exact (R.childState_connected_iff σ (fun _ => true) edge).mpr ⟨rfl, ha⟩

theorem childState_closed_of_one_active (σ : LiveState) (ω : Configuration edges)
    (edge : Fin edges) (hclosed : ω edge = false)
    (hactive : R.active σ ω (R.endpoint edge).1 = true ∨
      R.active σ ω (R.endpoint edge).2 = true) :
    R.childState σ ω edge = some .both ∨ R.childState σ ω edge = some .single := by
  simp only [childState, hclosed]
  cases ha : R.active σ ω (R.endpoint edge).1 <;>
    cases hb : R.active σ ω (R.endpoint edge).2 <;> simp_all

theorem childState_allClosed_single (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source) :
    R.childState .single (fun _ => false) edge = some .single := by
  have hn := R.loopless edge
  simp only [childState, active_single, reachableDecide_all_closed]
  rcases hincident with h | h
  · have hne : R.source ≠ (R.endpoint edge).2 := by simpa only [h] using hn
    simp [h, hne]
  · have hne : R.source ≠ (R.endpoint edge).1 := by simpa only [h] using hn.symm
    simp [h, hne]

end
end Universality.FiniteNetwork
