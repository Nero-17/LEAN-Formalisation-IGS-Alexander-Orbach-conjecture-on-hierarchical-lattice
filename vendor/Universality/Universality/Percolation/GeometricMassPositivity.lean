import Universality.Percolation.SimpleConfigurations
import Universality.Percolation.MassPositivity
import Universality.Matrix.UniversalPivotalVector

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem massMatrix_connected_column_pos_of_edge {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    (hfirst : (R.endpoint edge).1 ≠ R.target) (hsecond : (R.endpoint edge).2 ≠ R.target)
    (hconnected : R.crosses (fun _ => true) = true) :
    ∀ σ, 0 < R.massMatrix p σ .connected := by
  intro σ
  apply (R.massMatrix_pos_iff hp hp' σ .connected).mpr
  cases σ
  · exact ⟨fun _ => true, edge, hconnected, R.childState_allOpen .connected edge hincident⟩
  · refine ⟨onlyOpen edge, edge, ?_, R.childState_onlyOpen .both edge hincident⟩
    simp only [conditioning, R.crosses_onlyOpen_false edge hfirst hsecond, Bool.not_false]
  · refine ⟨onlyOpen edge, edge, ?_, R.childState_onlyOpen .single edge hincident⟩
    simp only [conditioning, R.crosses_onlyOpen_false edge hfirst hsecond, Bool.not_false]

theorem massMatrix_single_single_pos_of_edge {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source) :
    0 < R.massMatrix p .single .single := by
  apply (R.massMatrix_pos_iff hp hp' .single .single).mpr
  refine ⟨fun _ => false, edge, ?_, R.childState_allClosed_single edge hincident⟩
  simp only [conditioning, R.crosses_all_closed, Bool.not_false]

theorem massMatrix_connected_second_pos_of_edge {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    (hsurvives : R.crosses (onlyClosed edge) = true) :
    0 < 2 * R.massMatrix p .connected .both + R.massMatrix p .connected .single := by
  have hclosed : onlyClosed edge edge = false := by simp [onlyClosed]
  have hactive := R.active_at_incident_edge .connected (onlyClosed edge) edge hincident
  have hstate := R.childState_closed_of_one_active .connected (onlyClosed edge) edge hclosed hactive
  rcases hstate with hstate | hstate
  · have hb : 0 < R.massMatrix p .connected .both :=
      (R.massMatrix_pos_iff hp hp' .connected .both).mpr
        ⟨onlyClosed edge, edge, hsurvives, hstate⟩
    linarith [R.massMatrix_nonneg hp.le hp'.le .connected .single]
  · have hu : 0 < R.massMatrix p .connected .single :=
      (R.massMatrix_pos_iff hp hp' .connected .single).mpr
        ⟨onlyClosed edge, edge, hsurvives, hstate⟩
    linarith [R.massMatrix_nonneg hp.le hp'.le .connected .both]

/-- One nonterminal incident edge whose deletion leaves a terminal crossing
already forces strict positivity of the two-dimensional mass block. -/
theorem massPlaneBlock_pos_of_edge {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    (hfirst : (R.endpoint edge).1 ≠ R.target) (hsecond : (R.endpoint edge).2 ≠ R.target)
    (hsurvives : R.crosses (onlyClosed edge) = true) :
    ∀ i j, 0 < massPlaneBlock (R.massMatrix p) i j := by
  have hconnected : R.crosses (fun _ => true) = true :=
    R.crosses_mono (onlyClosed edge) (fun _ => true) (fun _ _ => rfl) hsurvives
  have hcolumn := R.massMatrix_connected_column_pos_of_edge hp hp' edge hincident
    hfirst hsecond hconnected
  have hsingle := R.massMatrix_single_single_pos_of_edge hp hp' edge hincident
  have hsecondcol := R.massMatrix_connected_second_pos_of_edge hp hp' edge hincident hsurvives
  intro i j
  fin_cases i <;> fin_cases j
  · exact hcolumn .connected
  · exact hsecondcol
  · exact hcolumn .single
  · change 0 < 2 * R.massMatrix p .single .both + R.massMatrix p .single .single
    linarith [R.massMatrix_nonneg hp.le hp'.le .single .both]

end
end Universality.FiniteNetwork
