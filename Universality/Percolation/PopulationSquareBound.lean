import Universality.Percolation.PopulationMartingale
import Universality.Percolation.RefinementVertexMean
import Universality.Probability.FiniteWeightSquare

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators

theorem liveResponse_nonneg {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (state : LiveState) (configuration : Configuration edges) (values : LiveState → ℝ)
    (hvalues : ∀ s, 0 ≤ values s) : 0 ≤ R.liveResponse state configuration values := by
  unfold liveResponse
  apply Finset.sum_nonneg
  intro edge _
  cases R.childState state configuration edge with
  | none => exact le_rfl
  | some s => exact hvalues s

theorem liveResponse_mono {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (state : LiveState) (configuration : Configuration edges) (values bounds : LiveState → ℝ)
    (hvalues : ∀ s, values s ≤ bounds s) :
    R.liveResponse state configuration values ≤ R.liveResponse state configuration bounds := by
  unfold liveResponse
  apply Finset.sum_le_sum
  intro edge _
  cases R.childState state configuration edge with
  | none => exact le_rfl
  | some s => exact hvalues s

end
end Universality.FiniteNetwork

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory
open scoped BigOperators

theorem population_pow_le_refined_vertex_pow (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (values : LiveState → ℝ) (hvalues : ∀ state, 0 ≤ values state) (order : ℕ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompare : ∀ state, values state ≤ bound * rule.network.conditionalVertexMass p state)
    (n : ℕ) (state : LiveState) (coarse : Configuration (rule.generation n).edges) :
    (rule.generation n).network.liveResponse state coarse values ^ order ≤
      bound ^ order * ∑ fine, refinementWeight rule p n coarse fine *
        ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ) ^ order := by
  have hmean : (rule.generation n).network.liveResponse state coarse values ≤
      bound * ∑ fine, refinementWeight rule p n coarse fine *
        ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ) := by
    rw [refinementWeight_vertexMass rule p hp hp' hfixed symmetry hs ht]
    calc
      _ ≤ (rule.generation n).network.liveResponse state coarse
          (bound • rule.network.conditionalVertexMass p) :=
        (rule.generation n).network.liveResponse_mono _ _ _ _ hcompare
      _ = bound * (rule.generation n).network.liveResponse state coarse
          (rule.network.conditionalVertexMass p) := FiniteNetwork.liveResponse_smul _ _ _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Nat.cast_nonneg _)) hbound
  have hsq := finite_weighted_mean_pow_le (refinementWeight rule p n coarse)
    (fun fine => ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ))
    (refinementWeight_nonneg rule p hp.le hp'.le n coarse)
    (sum_refinementWeight rule p hp hp' hfixed n coarse) (fun _ => Nat.cast_nonneg _) order
  calc
    _ ≤ (bound * ∑ fine, refinementWeight rule p n coarse fine *
        ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ)) ^ order :=
      pow_le_pow_left₀ ((rule.generation n).network.liveResponse_nonneg state coarse values hvalues) hmean order
    _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hsq (pow_nonneg hbound order)

theorem integral_population_pow_bound (rule : Rule)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (values : LiveState → ℝ) (hvalues : ∀ state, 0 ≤ values state) (order : ℕ)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompare : ∀ state, values state ≤ bound * rule.network.conditionalVertexMass p state)
    (n : ℕ) (state : LiveState) :
    (∫ path, weightedPopulation rule state values n (path n) ^ order
      ∂infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
        bound ^ order * (rule.generation (n + 1)).network.conditionalVertexMoment p state order := by
  have hright := integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
    (fun history => ∑ fine, refinementWeight rule p n (latest rule n history) fine *
      ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ) ^ order)
  calc
    _ ≤ ∫ path, bound ^ order * ∑ fine, refinementWeight rule p n (latest rule n (path n)) fine *
        ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) fine : ℝ) ^ order
        ∂infiniteLaw rule p hp hp' hfixed (state == .connected) := by
      apply integral_mono
        (integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
          (fun history => weightedPopulation rule state values n history ^ order))
        (hright.const_mul (bound ^ order))
      intro path
      exact population_pow_le_refined_vertex_pow rule p hp hp' hfixed symmetry hs ht values hvalues order
        bound hbound hcompare n state _
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_refinement_observable rule p hp hp' hfixed (state == .connected) n
        (fun next => ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both)
          (latest rule (n + 1) next) : ℝ) ^ order)).trans
        (integral_vertexMass_pow rule p hp hp' hfixed state (n + 1) order)

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory

theorem Classical.population_moment_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (values : LiveState → ℝ) (hvalues : ∀ state, 0 ≤ values state) (order : ℕ) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (∫ path, ConfigurationHistory.weightedPopulation rule state values n (path n) ^ order
          ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
        bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order * n) := by
  classical
  have hmass := rule.network.conditionalVertexMass_pos hp hp' (h.connected _) h.scale
  obtain ⟨largest, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun state => values state / rule.network.conditionalVertexMass p state) Finset.univ_nonempty
  let comparison := max 1 (values largest / rule.network.conditionalVertexMass p largest)
  have hcomparison : 0 < comparison := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcompare (state : LiveState) : values state ≤ comparison * rule.network.conditionalVertexMass p state := by
    apply (div_le_iff₀ (hmass state)).mp
    exact (hmax state (Finset.mem_univ state)).trans (le_max_right _ _)
  obtain ⟨momentBound, hmomentBound, hmoments⟩ := h.internal_vertex_moment_bounds p hp hp' hfixed order
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    lt_trans zero_lt_one ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  refine ⟨comparison ^ order * momentBound *
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ order,
    mul_pos (mul_pos (pow_pos hcomparison _) hmomentBound) (pow_pos hradius _), ?_⟩
  intro n state
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  calc
    _ ≤ comparison ^ order * (rule.generation (n + 1)).network.conditionalVertexMoment p state order :=
      ConfigurationHistory.integral_population_pow_bound rule p hp hp' hfixed symmetry hs ht
        values hvalues order comparison hcomparison.le hcompare n state
    _ ≤ comparison ^ order * (momentBound *
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order * (n + 1))) :=
      mul_le_mul_of_nonneg_left (hmoments (n + 1) state) (pow_nonneg hcomparison.le order)
    _ = _ := by rw [Nat.mul_add, pow_add]; ring

end
end Universality.Rule
