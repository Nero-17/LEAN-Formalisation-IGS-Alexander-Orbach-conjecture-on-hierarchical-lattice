import IGSIII34.Percolation.Network
import IGSIII34.Resistance.PathTrial
import Universality.Percolation.PivotalDimension

set_option autoImplicit false

namespace IGSIII34.Percolation
noncomputable section

def configurationResistance {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges) : ℝ :=
  (network rule configuration).effectiveResistance (fun _ => 1)

def conditionalMeanResistance {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (parameter : ℝ) : ℝ :=
  Universality.FiniteNetwork.expectation parameter
    (fun configuration => if rule.crosses configuration then
      configurationResistance rule configuration else 0) / rule.reliability parameter

theorem pivotalCount_le_configurationResistance {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Universality.FiniteNetwork.Configuration edges)
    (crosses : rule.crosses configuration = true) :
    (rule.pivotalCount configuration : ℝ) ≤ configurationResistance rule configuration := by
  classical
  have openPivotal (edge : Fin edges) (pivotal : rule.pivotal configuration edge = true) :
      configuration edge = true := by
    rw [← rule.pivotal_crosses_eq_state configuration edge pivotal]
    exact crosses
  let pivotalEquivalence : {edge : Fin edges // rule.pivotal configuration edge = true} ≃
      {edge : {edge : Fin edges // configuration edge = true} //
        rule.pivotal configuration edge.val = true} :=
    { toFun := fun edge => ⟨⟨edge.val, openPivotal edge.val edge.property⟩, edge.property⟩
      invFun := fun edge => ⟨edge.val.val, edge.property⟩
      left_inv := by intro edge; rfl
      right_inv := by intro edge; rfl }
  have countIdentity := Fintype.card_congr pivotalEquivalence
  simp only [Fintype.card_subtype] at countIdentity
  have bound := (network rule configuration).sum_pivotal_resistances_le_effectiveResistance
    ((network rule configuration).unitFlows_nonempty_of_connected
      (connected_of_crosses rule configuration crosses)) (resistance := fun _ => 1)
    (fun _ => zero_le_one)
    (Finset.univ.filter fun edge => rule.pivotal configuration edge.val = true)
    (by
      intro edge membership
      exact pivotal_disconnects_open_network rule configuration edge
        (Finset.mem_filter.mp membership).2)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, ← countIdentity,
    Universality.FiniteNetwork.pivotalCount, configurationResistance] using bound

theorem expectation_mono {edges : ℕ} {parameter : ℝ}
    (nonnegative : 0 ≤ parameter) (atMostOne : parameter ≤ 1)
    {first second : Universality.FiniteNetwork.Configuration edges → ℝ}
    (pointwise : ∀ configuration, first configuration ≤ second configuration) :
    Universality.FiniteNetwork.expectation parameter first ≤
      Universality.FiniteNetwork.expectation parameter second := by
  unfold Universality.FiniteNetwork.expectation
  apply Finset.sum_le_sum
  intro configuration _
  exact mul_le_mul_of_nonneg_left (pointwise configuration)
    (Universality.FiniteNetwork.bernoulliWeight_nonneg nonnegative atMostOne configuration)

theorem reliability_derivative_le_conditionalMeanResistance {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) {parameter : ℝ}
    (positive : 0 < parameter) (atMostOne : parameter ≤ 1)
    (fixedPoint : rule.reliability parameter = parameter) :
    deriv rule.reliability parameter ≤ conditionalMeanResistance rule parameter := by
  rw [← rule.conditional_connected_pivotalCount_at_fixed_point parameter fixedPoint positive.ne']
  apply div_le_div_of_nonneg_right _ (by rw [fixedPoint]; exact positive.le)
  apply expectation_mono positive.le atMostOne
  intro configuration
  by_cases crosses : rule.crosses configuration = true
  · simpa only [crosses, Bool.true_eq, ↓reduceIte] using
      pivotalCount_le_configurationResistance rule configuration crosses
  · simp [crosses]

/-- This uses the real generation networks of IGS II. Its generation zero is
the first substituted cell, hence the exponent `generation + 1`. -/
theorem generation_conditionalMeanResistance_lower_bound
    (rule : Universality.Rule) {parameter : ℝ}
    (positive : 0 < parameter) (atMostOne : parameter ≤ 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (generation : ℕ) :
    deriv rule.network.reliability parameter ^ (generation + 1) ≤
      conditionalMeanResistance (rule.generation generation).network parameter := by
  calc
    _ = deriv (rule.generation generation).network.reliability parameter :=
      (rule.generation_hasDerivAt parameter fixedPoint generation).deriv.symm
    _ ≤ _ := reliability_derivative_le_conditionalMeanResistance
      (rule.generation generation).network positive atMostOne
      (rule.generation_fixed_point parameter fixedPoint generation)

end
end IGSIII34.Percolation
