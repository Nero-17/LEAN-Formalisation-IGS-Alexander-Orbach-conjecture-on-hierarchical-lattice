import Universality.Percolation.MassSupportBranches
import Universality.Percolation.VertexMassResponse

namespace Universality.FiniteNetwork
noncomputable section
open Matrix
set_option maxHeartbeats 0

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem connected_response_allOpen_lower
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (values : LiveState → ℝ) (hvalues : ∀ state, 0 ≤ values state) :
    p ^ edges * ((edges : ℝ) * values .connected) ≤
      R.reliability p * (R.massMatrix p *ᵥ values) .connected := by
  have hpositive := (R.reliability_pos_iff_connected hp hp').mpr (hconnected _)
  have hcross : R.crosses (fun _ => true) = true := (R.crosses_eq_true _).mpr (hconnected _)
  have hnonneg (configuration : Configuration edges) :
      0 ≤ (if R.conditioning .connected configuration then
        bernoulliWeight p configuration * R.liveResponse .connected configuration values else 0) := by
    split
    · apply mul_nonneg (bernoulliWeight_nonneg hp.le hp'.le _)
      unfold liveResponse
      apply Finset.sum_nonneg
      intro edge _
      cases R.childState .connected configuration edge with
      | none => exact le_rfl
      | some state => exact hvalues state
    · exact le_rfl
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun configuration : Configuration edges => if R.conditioning .connected configuration then
      bernoulliWeight p configuration * R.liveResponse .connected configuration values else 0)
    (fun configuration _ => hnonneg configuration) (Finset.mem_univ (fun _ => true))
  have hlive : R.liveResponse .connected (fun _ => true) values = (edges : ℝ) * values .connected := by
    simp [liveResponse, R.childState_allOpen_connected hconnected]
  rw [R.massMatrix_mulVec_response, conditionalResponse, conditioningProbability_connected]
  rw [mul_div_cancel₀ _ hpositive.ne']
  simpa [conditioning, hcross, bernoulliWeight, hlive] using hsingle

end
end Universality.FiniteNetwork
