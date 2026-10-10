import Universality.Percolation.MassRowBounds

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
open Matrix
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def sourceIncidentEdges : Finset (Fin edges) :=
  Finset.univ.filter fun edge => (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source

theorem sourceIncidentEdges_card_lt_edges
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) : R.sourceIncidentEdges.card < edges := by
  obtain ⟨edge, hfirst, hsecond⟩ := R.exists_edge_avoiding_source hconnected hscale
  have hne : R.sourceIncidentEdges ≠ Finset.univ := by
    intro heq
    have hmem : edge ∈ R.sourceIncidentEdges := heq ▸ Finset.mem_univ _
    simpa [sourceIncidentEdges, hfirst, hsecond] using hmem
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
  simpa using hlt

theorem exists_open_source_incident_edge (configuration : Configuration edges)
    (hcross : R.crosses configuration = true) :
    ∃ edge ∈ R.sourceIncidentEdges, configuration edge = true := by
  obtain ⟨walk⟩ := (R.crosses_eq_true configuration).mp hcross
  have hexists {u v : Fin vertices} (walk : (R.openGraph configuration).Walk u v) (hne : u ≠ v) :
      ∃ edge, configuration edge = true ∧ ((R.endpoint edge).1 = u ∨ (R.endpoint edge).2 = u) := by
    cases walk with
    | nil => exact (hne rfl).elim
    | cons hadj tail =>
      obtain ⟨_, edge, hopen, h | h⟩ := hadj
      · exact ⟨edge, hopen, Or.inl (congrArg Prod.fst h)⟩
      · exact ⟨edge, hopen, Or.inr (congrArg Prod.snd h)⟩
  obtain ⟨edge, hopen, hincident⟩ := hexists walk R.terminals_distinct
  exact ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincident⟩, hopen⟩

theorem sourceIncidentEdges_card_ge_two
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) : 2 ≤ R.sourceIncidentEdges.card := by
  obtain ⟨edge, hincident⟩ := R.exists_source_incident_edge hconnected
  have hmem : edge ∈ R.sourceIncidentEdges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincident⟩
  obtain ⟨other, hother, hopen⟩ := R.exists_open_source_incident_edge (onlyClosed edge) (hcut edge)
  have hne : other ≠ edge := by
    intro heq
    subst other
    simp [onlyClosed] at hopen
  have hsubset : {edge, other} ⊆ R.sourceIncidentEdges := by
    intro element helement
    simp only [Finset.mem_insert, Finset.mem_singleton] at helement
    rcases helement with rfl | rfl
    · exact hmem
    · exact hother
  simpa [hne.symm] using Finset.card_le_card hsubset

theorem childState_incident_ne_none (state : LiveState) (configuration : Configuration edges)
    (edge : Fin edges) (hincident : edge ∈ R.sourceIncidentEdges) :
    R.childState state configuration edge ≠ none := by
  have hactive := R.active_at_incident_edge state configuration edge (Finset.mem_filter.mp hincident).2
  rcases hactive with hfirst | hsecond
  · cases hsecond : R.active state configuration (R.endpoint edge).2 <;> cases hopen : configuration edge <;>
      simp_all [childState]
  · cases hfirst : R.active state configuration (R.endpoint edge).1 <;> cases hopen : configuration edge <;>
      simp_all [childState]

theorem liveResponse_one_ge_incident (state : LiveState) (configuration : Configuration edges) :
    (R.sourceIncidentEdges.card : ℝ) ≤ R.liveResponse state configuration (fun _ => 1) := by
  classical
  rw [Finset.card_eq_sum_ones]
  push_cast
  unfold liveResponse
  calc
    _ = ∑ edge ∈ R.sourceIncidentEdges,
        (match R.childState state configuration edge with | none => (0 : ℝ) | some _ => 1) := by
      apply Finset.sum_congr rfl
      intro edge hmem
      have h := R.childState_incident_ne_none state configuration edge hmem
      cases hstate : R.childState state configuration edge <;> simp_all
    _ ≤ ∑ edge : Fin edges,
        (match R.childState state configuration edge with | none => (0 : ℝ) | some _ => 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun edge _ _ => by cases R.childState state configuration edge <;> norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro edge _
      cases R.childState state configuration edge <;> rfl

theorem liveResponse_allOpen_connected (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex) :
    R.liveResponse .connected (fun _ => true) (fun _ => 1) = edges := by
  have hactive (vertex : Fin vertices) : R.active .connected (fun _ => true) vertex = true := by
    simp only [active, show (LiveState.connected == LiveState.both) = false from rfl, Bool.false_and, Bool.or_false,
      SimpleGraph.reachableDecide_eq_true]
    exact hconnected vertex
  simp [liveResponse, childState, hactive]

theorem massMatrix_row_sum_ge_incident (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target) (state : LiveState) :
    (R.sourceIncidentEdges.card : ℝ) ≤ ∑ child, R.massMatrix p state child := by
  have hresponse : (∑ child, R.massMatrix p state child) =
      R.conditionalResponse p state (fun _ => 1) := by
    simpa [Matrix.mulVec, dotProduct] using R.massMatrix_mulVec_response p (fun _ => 1) state
  rw [hresponse, conditionalResponse]
  apply (le_div_iff₀ (R.conditioningProbability_pos_of_connected p hp hp' hconnected state)).mpr
  rw [conditioningProbability, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro configuration _
  split_ifs
  · simpa only [mul_comm (R.sourceIncidentEdges.card : ℝ)] using mul_le_mul_of_nonneg_left
      (R.liveResponse_one_ge_incident state configuration) (bernoulliWeight_pos hp hp' configuration).le
  · simp

theorem massMatrix_connected_row_sum_gt_incident (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    (R.sourceIncidentEdges.card : ℝ) < ∑ child, R.massMatrix p .connected child := by
  have hresponse : (∑ child, R.massMatrix p .connected child) =
      R.conditionalResponse p .connected (fun _ => 1) := by
    simpa [Matrix.mulVec, dotProduct] using R.massMatrix_mulVec_response p (fun _ => 1) .connected
  rw [hresponse, conditionalResponse]
  apply (lt_div_iff₀ (R.conditioningProbability_pos_of_connected p hp hp' (hconnected _) .connected)).mpr
  rw [conditioningProbability, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro configuration _
    split_ifs
    · simpa only [mul_comm (R.sourceIncidentEdges.card : ℝ)] using mul_le_mul_of_nonneg_left
        (R.liveResponse_one_ge_incident .connected configuration) (bernoulliWeight_pos hp hp' configuration).le
    · simp
  · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
    have hcross : R.crosses (fun _ => true) = true := (R.crosses_eq_true _).mpr (hconnected _)
    simp only [conditioning, hcross, ↓reduceIte, R.liveResponse_allOpen_connected hconnected]
    have hlt : (R.sourceIncidentEdges.card : ℝ) < edges := by
      exact_mod_cast R.sourceIncidentEdges_card_lt_edges (hconnected _) hscale
    simpa only [mul_comm (R.sourceIncidentEdges.card : ℝ)] using
      mul_lt_mul_of_pos_left hlt (bernoulliWeight_pos hp hp' (fun _ => true))

end
end Universality.FiniteNetwork
