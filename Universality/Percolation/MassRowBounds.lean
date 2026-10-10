import Universality.Percolation.GeometricPrimitivity
import Universality.Percolation.StrictReliability

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
open Matrix
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem liveResponse_one_le (state : LiveState) (configuration : Configuration edges) :
    R.liveResponse state configuration (fun _ => 1) ≤ (edges : ℝ) := by
  unfold liveResponse
  calc
    _ ≤ ∑ _ : Fin edges, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro edge _
      cases R.childState state configuration edge <;> norm_num
    _ = edges := by simp

theorem conditioningProbability_pos_of_connected (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target) (state : LiveState) :
    0 < R.conditioningProbability p state := by
  apply (R.conditioningProbability_pos_iff hp hp' state).mpr
  cases state
  · exact ⟨fun _ => true, (R.crosses_eq_true _).mpr hconnected⟩
  · exact ⟨fun _ => false, by simp [conditioning, R.crosses_all_closed]⟩
  · exact ⟨fun _ => false, by simp [conditioning, R.crosses_all_closed]⟩

theorem massMatrix_row_sum_le_edges (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target) (state : LiveState) :
    ∑ child, R.massMatrix p state child ≤ (edges : ℝ) := by
  have hresponse : (∑ child, R.massMatrix p state child) =
      R.conditionalResponse p state (fun _ => 1) := by
    simpa [Matrix.mulVec, dotProduct] using R.massMatrix_mulVec_response p (fun _ => 1) state
  rw [hresponse, conditionalResponse]
  apply (div_le_iff₀ (R.conditioningProbability_pos_of_connected p hp hp' hconnected state)).mpr
  rw [conditioningProbability, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro configuration _
  split_ifs
  · simpa only [mul_comm (edges : ℝ)] using mul_le_mul_of_nonneg_left
      (R.liveResponse_one_le state configuration) (bernoulliWeight_pos hp hp' configuration).le
  · simp

theorem exists_edge_avoiding_source
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    ∃ edge, (R.endpoint edge).1 ≠ R.source ∧ (R.endpoint edge).2 ≠ R.source := by
  let reversed : FiniteNetwork vertices edges :=
    { R with source := R.target, target := R.source, terminals_distinct := R.terminals_distinct.symm }
  have hconnected' : reversed.fullGraph.Reachable reversed.source reversed.target := hconnected.symm
  have hscale' : 1 < reversed.fullGraph.dist reversed.source reversed.target := by
    change 1 < R.fullGraph.dist R.target R.source
    rwa [SimpleGraph.dist_comm]
  obtain ⟨edge, hincident⟩ := reversed.exists_source_incident_edge hconnected'
  exact ⟨edge, reversed.incident_endpoints_ne_target edge hincident hscale'⟩

theorem liveResponse_allClosed_single_lt
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    R.liveResponse .single (fun _ => false) (fun _ => 1) < (edges : ℝ) := by
  obtain ⟨edge, hfirst, hsecond⟩ := R.exists_edge_avoiding_source hconnected hscale
  have hnone : R.childState .single (fun _ => false) edge = none := by
    simp [childState, active, reachableDecide_all_closed, hfirst, hsecond, Ne.symm hfirst, Ne.symm hsecond]
  unfold liveResponse
  calc
    _ < ∑ _ : Fin edges, (1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro other _
        cases R.childState .single (fun _ => false) other <;> norm_num
      · exact ⟨edge, Finset.mem_univ _, by rw [hnone]; norm_num⟩
    _ = edges := by simp

theorem massMatrix_single_row_sum_lt_edges (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    ∑ child, R.massMatrix p .single child < (edges : ℝ) := by
  have hresponse : (∑ child, R.massMatrix p .single child) =
      R.conditionalResponse p .single (fun _ => 1) := by
    simpa [Matrix.mulVec, dotProduct] using R.massMatrix_mulVec_response p (fun _ => 1) .single
  rw [hresponse, conditionalResponse]
  apply (div_lt_iff₀ (R.conditioningProbability_pos_of_connected p hp hp' hconnected .single)).mpr
  rw [conditioningProbability, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro configuration _
    split_ifs
    · simpa only [mul_comm (edges : ℝ)] using mul_le_mul_of_nonneg_left
        (R.liveResponse_one_le .single configuration) (bernoulliWeight_pos hp hp' configuration).le
    · simp
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp only [conditioning, R.crosses_all_closed, Bool.not_false, ↓reduceIte]
    simpa only [mul_comm (edges : ℝ)] using mul_lt_mul_of_pos_left
      (R.liveResponse_allClosed_single_lt hconnected hscale) (bernoulliWeight_pos hp hp' (fun _ => false))

end
end Universality.FiniteNetwork
