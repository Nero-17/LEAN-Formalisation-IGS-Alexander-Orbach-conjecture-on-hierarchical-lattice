import Universality.Percolation.RefinementVertexVariance
import Universality.Percolation.VertexRewardCompensation
import Universality.Percolation.PopulationSquareBound

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory
open scoped BigOperators

def vertexInnovation (rule : Rule) (p : ℝ) (state : LiveState) (n : ℕ)
    (next : rule.ConfigurationHistory (n + 1)) : ℝ :=
  ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) next.2 : ℝ) -
    ((rule.generation n).network.internalSelectedMass true (state == .both) (latest rule n next.1) : ℝ) -
    weightedPopulation rule state (rule.network.conditionalVertexMass p) n next.1

theorem vertexInnovation_eq_ae (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) (n : ℕ) :
    (fun path => vertexInnovation rule p state n (path (n + 1)))
      =ᵐ[infiniteLaw rule p hp hp' hfixed (state == .connected)] fun path =>
        vertexMass rule state (n + 1) path - vertexMass rule state n path -
          weightedPopulation rule state (rule.network.conditionalVertexMass p) n (path n) := by
  filter_upwards [infiniteLaw_extends rule p hp hp' hfixed (state == .connected)] with path hpath
  change ((rule.generation (n + 1)).network.internalSelectedMass true (state == .both) (path (n + 1)).2 : ℝ) -
    ((rule.generation n).network.internalSelectedMass true (state == .both) (latest rule n (path (n + 1)).1) : ℝ) -
    weightedPopulation rule state (rule.network.conditionalVertexMass p) n (path (n + 1)).1 = _
  rw [hpath n]
  rfl

theorem refinementWeight_vertexInnovation_sq_le (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (state : LiveState) (n : ℕ) (history : rule.ConfigurationHistory n) :
    (∑ fine, refinementWeight rule p n (latest rule n history) fine *
      vertexInnovation rule p state n (history, fine) ^ 2) ≤
      weightedPopulation rule state (fun child => rule.network.conditionalVertexMoment p child 2) n history := by
  classical
  change (∑ fine : Configuration ((rule.generation n).edges * rule.edges),
    (∏ e, rule.network.conditionalCellWeight p (latest rule n history e)
      (substitutionConfigurationEquiv.symm fine e)) *
    ((((rule.generation n).network.substitute rule.network).internalSelectedMass true (state == .both) fine : ℝ) -
      (rule.generation n).network.internalSelectedMass true (state == .both) (latest rule n history) -
      (rule.generation n).network.liveResponse state (latest rule n history) (rule.network.conditionalVertexMass p)) ^ 2) ≤ _
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  exact (rule.generation n).network.refinement_vertexMass_variance_le rule.network p
    (by rwa [hfixed]) (by rwa [hfixed]) symmetry hs ht (latest rule n history) state

theorem integral_vertexInnovation_sq_le (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source) (state : LiveState) (n : ℕ) :
    (∫ path, vertexInnovation rule p state n (path (n + 1)) ^ 2
      ∂infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
      ∫ path, weightedPopulation rule state (fun child => rule.network.conditionalVertexMoment p child 2) n (path n)
        ∂infiniteLaw rule p hp hp' hfixed (state == .connected) := by
  rw [← integral_refinement_observable rule p hp hp' hfixed (state == .connected) n
    (fun next => vertexInnovation rule p state n next ^ 2)]
  apply integral_mono
    (integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => ∑ fine, refinementWeight rule p n (latest rule n history) fine *
        vertexInnovation rule p state n (history, fine) ^ 2))
    (integrable_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (fun history => weightedPopulation rule state (fun child => rule.network.conditionalVertexMoment p child 2) n history))
  intro path
  exact refinementWeight_vertexInnovation_sq_le rule p hp hp' hfixed symmetry hs ht state n (path n)

end
end Universality.Rule.ConfigurationHistory

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory

theorem Classical.vertex_innovation_second_moment_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (∫ path, ConfigurationHistory.vertexInnovation rule p state n (path (n + 1)) ^ 2
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ≤
          bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
  obtain ⟨bound, hbound, hestimate⟩ := h.population_moment_bound p hp hp' hfixed
    (fun child => rule.network.conditionalVertexMoment p child 2)
    (fun child => rule.network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ 2) 1
  obtain ⟨symmetry, hs, ht⟩ := h.massAdmissible.symmetric
  refine ⟨bound, hbound, fun n state => ?_⟩
  apply (ConfigurationHistory.integral_vertexInnovation_sq_le rule p hp hp' hfixed symmetry hs ht state n).trans
  simpa only [pow_one, one_mul] using hestimate n state

end
end Universality.Rule
