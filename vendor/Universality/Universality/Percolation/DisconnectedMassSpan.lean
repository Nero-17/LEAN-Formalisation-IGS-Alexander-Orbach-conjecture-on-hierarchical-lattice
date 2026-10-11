import Universality.Percolation.VertexMassPositivity
import Universality.Percolation.ConditionalMassCharacteristic

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

/-- Closing every edge gives zero internal mass regardless of terminal selection. -/
theorem internalSelectedMass_allClosed (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) :
    R.internalSelectedMass sourceSelected targetSelected (fun _ => false) = 0 := by
  unfold internalSelectedMass
  apply Finset.sum_eq_zero
  intro vertex _
  have hsource : R.source ≠ vertex.val := vertex.property.1.symm
  have htarget : R.target ≠ vertex.val := vertex.property.2.symm
  simp [selectedActive, R.reachableDecide_all_closed, hsource, htarget]

/-- A single open edge from the source to an internal vertex gives exactly
one selected internal vertex, also when both terminals are selected. -/
theorem internalSelectedMass_onlyOpen_source_first (R : FiniteNetwork vertices edges)
    (edge : Fin edges) (hsource : (R.endpoint edge).1 = R.source)
    (htarget : (R.endpoint edge).2 ≠ R.target) (targetSelected : Bool) :
    R.internalSelectedMass true targetSelected (onlyOpen edge) = 1 := by
  classical
  have hdistinct : (R.endpoint edge).2 ≠ R.source := by
    simpa only [hsource] using (R.loopless edge).symm
  let vertex : R.InteriorVertex := ⟨(R.endpoint edge).2, hdistinct, htarget⟩
  have hselected (other : R.InteriorVertex) :
      R.selectedActive true targetSelected (onlyOpen edge) other.val = decide (other = vertex) := by
    apply Bool.eq_iff_iff.mpr
    simp only [selectedActive, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      SimpleGraph.reachableDecide_eq_true, R.reachable_onlyOpen_iff, decide_eq_true_eq]
    have hotherSource := other.property.1
    have hotherTarget := other.property.2
    have hne := R.terminals_distinct
    have heq : other = vertex ↔ other.val = (R.endpoint edge).2 := by
      exact Subtype.ext_iff
    rw [heq]
    aesop
  unfold internalSelectedMass
  simp_rw [hselected]
  simp

theorem internalSelectedMass_onlyOpen_source_second (R : FiniteNetwork vertices edges)
    (edge : Fin edges) (hsource : (R.endpoint edge).2 = R.source)
    (htarget : (R.endpoint edge).1 ≠ R.target) (targetSelected : Bool) :
    R.internalSelectedMass true targetSelected (onlyOpen edge) = 1 := by
  classical
  have hdistinct : (R.endpoint edge).1 ≠ R.source := by
    simpa only [hsource] using R.loopless edge
  let vertex : R.InteriorVertex := ⟨(R.endpoint edge).1, hdistinct, htarget⟩
  have hselected (other : R.InteriorVertex) :
      R.selectedActive true targetSelected (onlyOpen edge) other.val = decide (other = vertex) := by
    apply Bool.eq_iff_iff.mpr
    simp only [selectedActive, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true,
      SimpleGraph.reachableDecide_eq_true, R.reachable_onlyOpen_iff, decide_eq_true_eq]
    have hotherSource := other.property.1
    have hotherTarget := other.property.2
    have hne := R.terminals_distinct
    have heq : other = vertex ↔ other.val = (R.endpoint edge).1 := by
      exact Subtype.ext_iff
    rw [heq]
    aesop
  unfold internalSelectedMass
  simp_rw [hselected]
  simp

/-- Both noncrossing conditional masses contain consecutive lattice values
zero and one with positive conditional probability. -/
theorem disconnected_mass_consecutive_configurations (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) (targetSelected : Bool) :
    ∃ first second : Configuration edges,
      0 < R.conditionalCellWeight p false first ∧
      0 < R.conditionalCellWeight p false second ∧
      R.internalSelectedMass true targetSelected first = 0 ∧
      R.internalSelectedMass true targetSelected second = 1 := by
  obtain ⟨edge, hincident⟩ := R.exists_source_incident_edge hconnected
  obtain ⟨hfirst, hsecond⟩ := R.incident_endpoints_ne_target edge hincident hscale
  refine ⟨(fun _ => false), onlyOpen edge, ?_, ?_, R.internalSelectedMass_allClosed _ _, ?_⟩
  · simp only [conditionalCellWeight, R.crosses_all_closed, if_pos rfl, Bool.false_eq_true,
      ↓reduceIte, hfixed]
    exact div_pos (bernoulliWeight_pos hp hp' _) (sub_pos.mpr hp')
  · simp only [conditionalCellWeight, R.crosses_onlyOpen_false edge hfirst hsecond,
      if_pos rfl, Bool.false_eq_true, ↓reduceIte, hfixed]
    exact div_pos (bernoulliWeight_pos hp hp' _) (sub_pos.mpr hp')
  · rcases hincident with hleft | hright
    · exact R.internalSelectedMass_onlyOpen_source_first edge hleft hsecond targetSelected
    · exact R.internalSelectedMass_onlyOpen_source_second edge hright hfirst targetSelected

end
end Universality.FiniteNetwork
