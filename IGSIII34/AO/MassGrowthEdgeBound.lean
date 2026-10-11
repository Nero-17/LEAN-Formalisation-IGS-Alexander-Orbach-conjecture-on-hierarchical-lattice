import IGSIII34.AO.ActualMass
import Mathlib.Data.Finset.Max

set_option autoImplicit false
namespace IGSIII34.AO
noncomputable section
open Universality Universality.FiniteNetwork Matrix
open scoped BigOperators

theorem conditionalResponse_le_edges_mul_bound
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (probability : ℝ) (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1)
    (state : LiveState) (values : LiveState → ℝ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound) (bounded : ∀ child, values child ≤ bound) :
    network.conditionalResponse probability state values ≤ (edges : ℝ) * bound := by
  have responseBound (configuration : Configuration edges) :
      network.liveResponse state configuration values ≤ (edges : ℝ) * bound := by
    calc
      _ ≤ ∑ _edge : Fin edges, bound := by
        apply Finset.sum_le_sum
        intro edge _
        cases network.childState state configuration edge with
        | none => exact boundNonnegative
        | some child => exact bounded child
      _ = _ := by simp
  by_cases zero : network.conditioningProbability probability state = 0
  · simp only [conditionalResponse, zero, div_zero]
    exact mul_nonneg (Nat.cast_nonneg _) boundNonnegative
  · have positive : 0 < network.conditioningProbability probability state :=
      lt_of_le_of_ne (network.conditioningProbability_nonneg nonnegative atMostOne state) (Ne.symm zero)
    unfold conditionalResponse
    apply (div_le_iff₀ positive).mpr
    calc
      _ ≤ ∑ configuration : Configuration edges,
          if network.conditioning state configuration then
            bernoulliWeight probability configuration * ((edges : ℝ) * bound) else 0 := by
        apply Finset.sum_le_sum
        intro configuration _
        split_ifs
        · exact mul_le_mul_of_nonneg_left (responseBound configuration)
            (bernoulliWeight_nonneg nonnegative atMostOne configuration)
        · exact le_rfl
      _ = (edges : ℝ) * bound * network.conditioningProbability probability state := by
        unfold conditioningProbability
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro configuration _
        split_ifs <;> ring

/-- The actual three-state mass Perron multiplier cannot exceed the number
of labelled replacement edges. No criticality assumption is required. -/
theorem classical_mass_spectralRadius_le_edges
    (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1) :
    (spectralRadius ℂ ((rule.network.massMatrix probability).map Complex.ofReal)).toReal ≤
      (rule.edges : ℝ) := by
  obtain ⟨_, vector, vectorPositive, eigenvector⟩ :=
    classicalRule.mass_spectralRadius_positive_eigenvector probability positive belowOne
  obtain ⟨largest, _, maximal⟩ := Finset.exists_max_image Finset.univ vector Finset.univ_nonempty
  have bounded := conditionalResponse_le_edges_mul_bound rule.network probability positive.le belowOne.le
    largest vector (vector largest) (vectorPositive largest).le (fun child => maximal child (Finset.mem_univ child))
  have equation := congrFun eigenvector largest
  rw [rule.network.massMatrix_mulVec_response] at equation
  simp only [Pi.smul_apply, smul_eq_mul] at equation
  rw [equation] at bounded
  exact (mul_le_mul_iff_of_pos_right (vectorPositive largest)).mp bounded

end
end IGSIII34.AO
