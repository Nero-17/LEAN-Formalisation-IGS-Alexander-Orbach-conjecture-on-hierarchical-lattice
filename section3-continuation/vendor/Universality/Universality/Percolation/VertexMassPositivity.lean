import Universality.Percolation.VertexMassResponse
import Universality.Percolation.FiniteMassDimension

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem internalSelectedMass_pos_of_active (σ : LiveState) (ω : Configuration edges)
    (v : R.InteriorVertex) (hactive : R.active σ ω v.val = true) :
    0 < R.internalSelectedMass true (σ == .both) ω := by
  unfold internalSelectedMass
  apply Finset.sum_pos'
  · intro _ _; positivity
  · refine ⟨v, Finset.mem_univ v, ?_⟩
    have hselected : R.selectedActive true (σ == .both) ω v.val = true := by
      simpa only [selectedActive, Bool.true_and, active] using hactive
    simp only [hselected, ↓reduceIte]; omega

theorem internalSelectedMass_pos_of_open_incident (σ : LiveState) (ω : Configuration edges)
    (edge : Fin edges) (hopen : ω edge = true)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    (hfirst : (R.endpoint edge).1 ≠ R.target) (hsecond : (R.endpoint edge).2 ≠ R.target) :
    0 < R.internalSelectedMass true (σ == .both) ω := by
  have heq := R.active_endpoints_eq_of_open σ ω edge hopen
  rcases hincident with hsource | hsource
  · have hne : (R.endpoint edge).2 ≠ R.source := by
      simpa only [hsource] using (R.loopless edge).symm
    apply R.internalSelectedMass_pos_of_active σ ω ⟨(R.endpoint edge).2, hne, hsecond⟩
    rw [← heq, hsource]
    exact R.active_root σ ω
  · have hne : (R.endpoint edge).1 ≠ R.source := by
      simpa only [hsource] using R.loopless edge
    apply R.internalSelectedMass_pos_of_active σ ω ⟨(R.endpoint edge).1, hne, hfirst⟩
    rw [heq, hsource]
    exact R.active_root σ ω

theorem conditionalVertexMass_pos_of_configuration {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (σ : LiveState) (ω : Configuration edges) (hcondition : R.conditioning σ ω = true)
    (hmass : 0 < R.internalSelectedMass true (σ == .both) ω) :
    0 < R.conditionalVertexMass p σ := by
  unfold conditionalVertexMass conditionalInternalMean
  apply Finset.sum_pos'
  · intro configuration _
    exact mul_nonneg (R.conditionalCellWeight_nonneg hp.le hp'.le _ _) (Nat.cast_nonneg _)
  · refine ⟨ω, Finset.mem_univ ω, ?_⟩
    rw [R.conditionalCellWeight_reference, hcondition, if_pos rfl]
    apply mul_pos
    · exact div_pos (bernoulliWeight_pos hp hp' ω)
        ((R.conditioningProbability_pos_iff hp hp' σ).mpr ⟨ω, hcondition⟩)
    · exact_mod_cast hmass

/-- Geometric, rather than assumed, positivity of the internal-vertex reward.
Terminal distance at least two supplies a source-adjacent internal vertex. -/
theorem conditionalVertexMass_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) (σ : LiveState) :
    0 < R.conditionalVertexMass p σ := by
  obtain ⟨edge, hincident⟩ := R.exists_source_incident_edge hconnected
  obtain ⟨hfirst, hsecond⟩ := R.incident_endpoints_ne_target edge hincident hscale
  cases σ
  · apply R.conditionalVertexMass_pos_of_configuration hp hp' .connected (fun _ => true)
    · exact (R.crosses_eq_true _).mpr hconnected
    · exact R.internalSelectedMass_pos_of_open_incident _ _ edge rfl hincident hfirst hsecond
  · apply R.conditionalVertexMass_pos_of_configuration hp hp' .both (onlyOpen edge)
    · simp only [conditioning, R.crosses_onlyOpen_false edge hfirst hsecond, Bool.not_false]
    · exact R.internalSelectedMass_pos_of_open_incident _ _ edge (by simp [onlyOpen]) hincident hfirst hsecond
  · apply R.conditionalVertexMass_pos_of_configuration hp hp' .single (onlyOpen edge)
    · simp only [conditioning, R.crosses_onlyOpen_false edge hfirst hsecond, Bool.not_false]
    · exact R.internalSelectedMass_pos_of_open_incident _ _ edge (by simp [onlyOpen]) hincident hfirst hsecond

end
end Universality.FiniteNetwork
