import Universality.Percolation.InfiniteObservables
import Universality.Percolation.VertexMomentGrowth
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem memLp_infiniteLaw_observable (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (opened : Bool) (n : ℕ)
    (observable : rule.ConfigurationHistory n → ℝ) (r : ℝ≥0∞) :
    MemLp (fun path => observable (path n)) r (infiniteLaw rule p hp hp' hfixed opened) := by
  apply MemLp.of_bound
    (((measurable_of_countable observable).comp (measurable_pi_apply n)).aestronglyMeasurable)
    (∑ history, ‖observable history‖)
  exact Filter.Eventually.of_forall (fun path =>
    Finset.single_le_sum (fun history _ => norm_nonneg (observable history)) (Finset.mem_univ (path n)))

/-- Actual internal selected-vertex counts, on the coherent infinite history space. -/
def vertexMass (rule : Rule) (state : LiveState) (n : ℕ)
    (path : Π k, rule.ConfigurationHistory k) : ℝ :=
  ((rule.generation n).network.internalSelectedMass true (state == .both)
    (latest rule n (path n)) : ℝ)

theorem integral_vertexMass_pow (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) (n r : ℕ) :
    ∫ path, vertexMass rule state n path ^ r
        ∂infiniteLaw rule p hp hp' hfixed (state == .connected) =
      (rule.generation n).network.conditionalVertexMoment p state r := by
  unfold vertexMass
  rw [integral_infiniteLaw rule p hp hp' hfixed (state == .connected) n
    (fun history => ((rule.generation n).network.internalSelectedMass true (state == .both)
      (latest rule n history) : ℝ) ^ r)]
  simp only [latest_ofFine, conditionalVertexMoment, conditionalInternalMoment]

theorem memLp_vertexMass (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) (n : ℕ) (r : ℝ≥0∞) :
    MemLp (vertexMass rule state n) r
      (infiniteLaw rule p hp hp' hfixed (state == .connected)) :=
  memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
    (fun history => ((rule.generation n).network.internalSelectedMass true (state == .both)
      (latest rule n history) : ℝ)) r

theorem integral_normalized_vertexMass_pow (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) (n r : ℕ) (scale : ℝ) :
    ∫ path, (vertexMass rule state n path / scale ^ n) ^ r
        ∂infiniteLaw rule p hp hp' hfixed (state == .connected) =
      (rule.generation n).network.conditionalVertexMoment p state r / scale ^ (n * r) := by
  simp_rw [div_pow, ← pow_mul]
  rw [integral_div, integral_vertexMass_pow]

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory

/-- Uniform bounds on all normalized moments in a single probability space
for each terminal state. This does not assert convergence of the masses. -/
theorem Classical.infinite_normalized_vertex_moment_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∀ r : ℕ, ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      ∫ path, (ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) ^ r
          ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected) ≤ bound := by
  intro r
  obtain ⟨bound, hbound, hestimate⟩ := h.internal_vertex_moment_bounds p hp hp' hfixed r
  refine ⟨bound, hbound, fun n state => ?_⟩
  rw [ConfigurationHistory.integral_normalized_vertexMass_pow]
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_trans zero_lt_one ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  apply (div_le_iff₀ (pow_pos hradius _)).mpr
  simpa only [Nat.mul_comm n r] using hestimate n state

end
end Universality.Rule
