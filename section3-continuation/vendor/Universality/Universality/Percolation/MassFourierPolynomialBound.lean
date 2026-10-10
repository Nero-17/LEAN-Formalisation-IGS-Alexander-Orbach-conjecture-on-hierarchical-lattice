import Universality.Percolation.GlobalMassFourierCover
import Universality.Probability.CharacteristicPolynomialBound

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- Uniform polynomial Fourier decay of every order for the actual finite
mass laws throughout their expanding fundamental lattice intervals. -/
theorem Classical.internal_mass_fourier_polynomial_bound {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ depth : ℕ, ∀ n ≥ depth, ∀ state t,
      1 ≤ |t| →
      |t| ≤ Real.pi * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n →
      ‖(rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)‖ *
          |t| ^ order ≤ constant := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  obtain ⟨bound, hb0, hb1, depth, hcover⟩ := h.internal_mass_global_fourier_cover p hp hp' hfixed
  obtain ⟨constant, hc, hpolynomial⟩ := characteristic_polynomial_bound radius bound
    rule.network.sourceIncidentEdges.card order (zero_lt_one.trans hradius) hb0 hb1
    (rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut)
  refine ⟨constant, hc, depth, ?_⟩
  intro n hn state t ht htpi
  exact hpolynomial _ t (norm_nonneg _) (hcover n hn state t ht htpi)

end
end Universality.Rule
