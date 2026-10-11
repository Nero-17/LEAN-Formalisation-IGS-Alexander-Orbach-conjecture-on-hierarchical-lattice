import Universality.Graph.ClassicalRule
import Universality.Percolation.RenormalisationLimits

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.existsUnique_interior_fixed_point {rule : Rule} (h : rule.Classical) :
    ∃! p : ℝ, 0 < p ∧ p < 1 ∧ rule.network.reliability p = p := by
  obtain ⟨p, hp, hp', hfixed⟩ := h.exists_interior_fixed_point
  refine ⟨p, ⟨hp, hp', hfixed⟩, ?_⟩
  intro q hq
  exact rule.network.interior_fixed_point_unique q p hq.1 hq.2.1 hp hp' hq.2.2 hfixed h.scale

/-- The strict dimension inequalities for the actual finite-growth formulas.
No almost-sure or bulk infinite-cluster statement is included. -/
theorem Classical.pivotal_mass_inequalities {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    0 < Real.log (deriv rule.network.reliability p) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) ∧
    Real.log (deriv rule.network.reliability p) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) <
    Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target) := by
  have hderivative := rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale
  have hscale : 0 < Real.log
      (rule.network.fullGraph.dist rule.network.source rule.network.target) :=
    Real.log_pos (by exact_mod_cast h.scale)
  have hdominance := rule.interior_fixed_point_spectral_dominance p hp hp' hfixed
    h.massAdmissible.symmetric h.scale
  exact ⟨div_pos (Real.log_pos hderivative) hscale,
    (div_lt_div_iff_of_pos_right hscale).mpr
      (Real.log_lt_log hdominance.1 hdominance.2.1)⟩

/-- A complete finite crossing transition: one internal fixed point, strict
instability there, and convergence of the actual finite-network crossing
probabilities to zero or one on its two sides. -/
theorem Classical.finite_crossing_transition {rule : Rule} (h : rule.Classical) :
    ∃ critical : ℝ, 0 < critical ∧ critical < 1 ∧
      rule.network.reliability critical = critical ∧
      1 < deriv rule.network.reliability critical ∧
      (∀ p, 0 ≤ p → p < critical →
        Tendsto (fun n : ℕ => (rule.generation n).network.reliability p) atTop (𝓝 0)) ∧
      (∀ p, critical < p → p ≤ 1 →
        Tendsto (fun n : ℕ => (rule.generation n).network.reliability p) atTop (𝓝 1)) ∧
      (∀ p, 0 < p → p < 1 → rule.network.reliability p = p → p = critical) := by
  obtain ⟨critical, hc, hc', hfixed⟩ := h.exists_interior_fixed_point
  refine ⟨critical, hc, hc', hfixed,
    rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale,
    ?_, ?_, ?_⟩
  · intro p hp hpc
    exact rule.generation_crossing_tendsto_zero critical p hc hc' hfixed hp hpc h.scale
  · intro p hpc hp'
    exact rule.generation_crossing_tendsto_one critical p hc hc' hfixed hpc hp' h.scale
  · intro p hp hp' hfp
    exact rule.network.interior_fixed_point_unique p critical hp hp' hc hc' hfp hfixed h.scale

end
end Universality.Rule
