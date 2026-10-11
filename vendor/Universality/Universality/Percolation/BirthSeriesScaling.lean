import Universality.Percolation.AnnealedFiniteBirthMoments
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality
noncomputable section

theorem discounted_power_identity (edges growth coefficient : ℝ) (hedges : 0 < edges) (order depth : ℕ) :
    (1 / edges) ^ (depth + 2) * (coefficient * growth ^ (order * depth)) =
      (coefficient / edges ^ 2) * (growth ^ order / edges) ^ depth := by
  simp only [div_pow, one_pow, pow_add, pow_mul]
  field_simp [hedges.ne']
  <;> ring

namespace Rule

theorem weighted_birth_tail_scaling (rule : Rule) (p growth constant : ℝ) (order offset : ℕ)
    (hedges : 0 < (rule.edges : ℝ))
    (hs : Summable (fun j : ℕ => (1 / (rule.edges : ℝ)) ^ j *
      rule.expectedClusterBirthPower p order (offset + j + 1)))
    (hb : (∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ j *
      rule.expectedClusterBirthPower p order (offset + j + 1)) ≤ constant * growth ^ (order * offset)) :
    Summable (fun j : ℕ => (1 / (rule.edges : ℝ)) ^ ((offset + j) + 2) *
      rule.expectedClusterBirthPower p order ((offset + j) + 1)) ∧
    (∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ ((offset + j) + 2) *
      rule.expectedClusterBirthPower p order ((offset + j) + 1)) ≤
      (constant / (rule.edges : ℝ) ^ 2) * (growth ^ order / rule.edges) ^ offset := by
  have heq (j : ℕ) : (1 / (rule.edges : ℝ)) ^ (offset + 2) *
      ((1 / (rule.edges : ℝ)) ^ j * rule.expectedClusterBirthPower p order (offset + j + 1)) =
      (1 / (rule.edges : ℝ)) ^ ((offset + j) + 2) * rule.expectedClusterBirthPower p order ((offset + j) + 1) := by
    rw [show offset + j + 2 = (offset + 2) + j by omega, pow_add]
    ring
  refine ⟨(hs.mul_left ((1 / (rule.edges : ℝ)) ^ (offset + 2))).congr heq, ?_⟩
  have hsum : (∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ ((offset + j) + 2) *
      rule.expectedClusterBirthPower p order ((offset + j) + 1)) =
      (1 / (rule.edges : ℝ)) ^ (offset + 2) *
        ∑' j : ℕ, (1 / (rule.edges : ℝ)) ^ j * rule.expectedClusterBirthPower p order (offset + j + 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => (heq j).symm)
  rw [hsum]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (one_div_nonneg.mpr hedges.le) _)).trans_eq
    (discounted_power_identity (rule.edges : ℝ) growth constant hedges order offset)

end Rule
end
end Universality
