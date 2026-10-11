import Universality.Percolation.VertexMomentGrowth
import Universality.Probability.FiniteWeightSquare

namespace Universality.FiniteNetwork
noncomputable section

theorem conditionalVertexMass_pow_le_moment {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (state : LiveState) (order : ℕ) :
    R.conditionalVertexMass p state ^ order ≤ R.conditionalVertexMoment p state order := by
  exact finite_weighted_mean_pow_le
    (R.conditionalCellWeight p (state == .connected))
    (fun configuration => (R.internalSelectedMass true (state == .both) configuration : ℝ))
    (R.conditionalCellWeight_nonneg hp hp' _)
    (R.sum_conditionalCellWeight p hpositive hless _)
    (fun _ => Nat.cast_nonneg _) order

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

/-- All integer moments of actual conditional internal mass have matching
upper and lower spectral growth, uniformly over generations and states. -/
theorem Classical.internal_vertex_moment_comparison {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ n state,
      lower * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order * n) ≤
        (rule.generation n).network.conditionalVertexMoment p state order ∧
      (rule.generation n).network.conditionalVertexMoment p state order ≤
        upper * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (order * n) := by
  obtain ⟨lower, _, hlower, _, hbounds⟩ := h.internal_vertex_mass_bounds p hp hp' hfixed
  obtain ⟨upper, hupper, hupperBound⟩ := h.internal_vertex_moment_bounds p hp hp' hfixed order
  refine ⟨lower ^ order, upper, pow_pos hlower _, hupper, ?_⟩
  intro n state
  refine ⟨?_, hupperBound n state⟩
  have hmean := (hbounds n state).1
  have hpower := pow_le_pow_left₀ (by positivity) hmean order
  have hjensen := (rule.generation n).network.conditionalVertexMass_pow_le_moment p hp.le hp'.le
    (by rwa [rule.generation_fixed_point p hfixed n])
    (by rwa [rule.generation_fixed_point p hfixed n]) state order
  calc
    _ ≤ (rule.generation n).network.conditionalVertexMass p state ^ order := by
      simpa only [mul_pow, ← pow_mul, Nat.mul_comm n order] using hpower
    _ ≤ _ := hjensen

theorem Classical.internal_vertex_moment_logarithmic_growth {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) (state : LiveState) :
    Tendsto (fun n : ℕ =>
      Real.log ((rule.generation n).network.conditionalVertexMoment p state order) / n)
      atTop (𝓝 ((order : ℝ) * Real.log
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    h.internal_vertex_moment_comparison p hp hp' hfixed order
  have hr := (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
    (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hlimit := logarithmic_growth_of_bounds
    (fun n => (rule.generation n).network.conditionalVertexMoment p state order)
    (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ order)
    lower upper (pow_pos (lt_trans zero_lt_one hr) _) hlower hupper
    (fun n => by simpa only [← pow_mul] using hbounds n state)
  simpa only [Real.log_pow] using hlimit

end
end Universality.Rule
