import IGSIII.Mass.GeometricReward
import Universality.Percolation.VertexNoiseLimit

set_option autoImplicit false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- The actual birth innovations on the coherent configuration space have
negligible cumulative error along the full sequence, almost surely. -/
theorem Classical.vertex_innovation_sum_ae_zero {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (state : LiveState) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
      Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.range n, ConfigurationHistory.vertexInnovation rule p state k (path (k + 1))) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 0) := by
  obtain ⟨bound, bound_positive, estimate⟩ :=
    classicalRule.vertex_innovation_second_moment_bound p positive below_one fixed_point
  apply IGSIII.Mass.ae_normalized_sum_zero_of_second_moment_bound _ _ bound _ bound_positive.le
    ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  · exact fun n => estimate n state
  · intro n
    exact ConfigurationHistory.memLp_infiniteLaw_observable rule p positive below_one fixed_point
      (state == .connected) (n + 1) (ConfigurationHistory.vertexInnovation rule p state n) 2

/-- Almost-sure birth-reward compensation for the actual graph process.
This strengthens the existing L² compensation theorem without assuming the
desired mass limit or an almost-sure error certificate. -/
theorem Classical.vertex_reward_compensation_ae_zero {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) (state : LiveState) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
      Tendsto (fun n : ℕ =>
        (ConfigurationHistory.vertexMass rule state n path - ConfigurationHistory.vertexMass rule state 0 path -
          ∑ k ∈ Finset.range n, ConfigurationHistory.weightedPopulation rule state
            (rule.network.conditionalVertexMass p) k (path k)) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 0) := by
  have identities := ae_all_iff.mpr (fun k => ConfigurationHistory.vertexInnovation_eq_ae
    rule p positive below_one fixed_point state k)
  filter_upwards [classicalRule.vertex_innovation_sum_ae_zero p positive below_one fixed_point state,
    identities] with path convergence identity
  convert convergence using 1
  ext n
  simp_rw [identity]
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun k => ConfigurationHistory.vertexMass rule state k path) n]

end Universality.Rule
