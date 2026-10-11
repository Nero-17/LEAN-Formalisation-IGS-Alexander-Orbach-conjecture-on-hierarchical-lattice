import Universality.Percolation.VertexMassConvergence
import Universality.Probability.NonnegativeL2Limit

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem Classical.nonnegative_internal_vertex_mass_L2_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected), 0 ≤ limit path) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
        2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  obtain ⟨limit, hlimit, hmean, hconv⟩ := h.internal_vertex_mass_L2_limit p hp hp' hfixed state
  refine ⟨limit, hlimit, ?_, hmean, hconv⟩
  exact nonnegative_L2_limit
    (fun n path => ConfigurationHistory.vertexMass rule state n path /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) limit
    (fun n => (memLp_div_const_real
      (ConfigurationHistory.memLp_vertexMass rule p hp hp' hfixed state n 2) _).aestronglyMeasurable)
    hlimit.aestronglyMeasurable
    (fun n path => div_nonneg (Nat.cast_nonneg _) (pow_nonneg ENNReal.toReal_nonneg n)) hconv

end
end Universality.Rule
