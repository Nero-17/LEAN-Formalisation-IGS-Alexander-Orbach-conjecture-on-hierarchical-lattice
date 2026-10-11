import Universality.Percolation.CharacteristicAnnulus
import Universality.Percolation.CharacteristicIteration

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual bounded-annulus gap propagates through arbitrarily many
additional substitution levels by an iterated terminal-degree power. -/
theorem Classical.internal_mass_annular_fourier_decay {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : lower ≤ upper) :
    ∃ bound : ℝ, 0 ≤ bound ∧ bound < 1 ∧ ∃ depth : ℕ,
      ∀ n ≥ depth, ∀ extra : ℕ, ∀ state t, lower ≤ |t| → |t| ≤ upper →
      ‖(rule.generation (n + extra)).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)‖ ≤
          bound ^ (rule.network.sourceIncidentEdges.card ^ extra) := by
  obtain ⟨bound, hbound0, hbound1, hevent⟩ :=
    h.internal_mass_characteristic_annulus p hp hp' hfixed lower upper hlower hupper
  obtain ⟨depth, hdepth⟩ := eventually_atTop.mp hevent
  refine ⟨bound, hbound0, hbound1, depth, ?_⟩
  intro n hn extra state t htLower htUpper
  exact rule.generation_characteristic_norm_iterate h.massAdmissible.symmetric p hp hp' hfixed n
    (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
    bound hbound0 hbound1.le (fun child => hdepth n hn child t htLower htUpper) extra state

end
end Universality.Rule

