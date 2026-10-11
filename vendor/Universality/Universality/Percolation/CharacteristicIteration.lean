import Universality.Percolation.CharacteristicContraction

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Iterating the actual offspring contraction gives a double-exponential
power in the number of extra substitution levels, at a fixed raw frequency. -/
theorem generation_characteristic_norm_iterate (rule : Rule) (hsymmetric : rule.TerminalSymmetric)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n : ℕ) (t bound : ℝ) (hbound0 : 0 ≤ bound) (hbound1 : bound ≤ 1)
    (hvalues : ∀ child, ‖(rule.generation n).network.conditionalVertexCharacteristic p child t‖ ≤ bound)
    (extra : ℕ) (state : LiveState) :
    ‖(rule.generation (n + extra)).network.conditionalVertexCharacteristic p state t‖ ≤
      bound ^ (rule.network.sourceIncidentEdges.card ^ extra) := by
  induction extra generalizing state with
  | zero => simpa using hvalues state
  | succ extra ih =>
    have hstep := rule.generation_characteristic_norm_bound hsymmetric p hp hp' hfixed
      (n + extra) t (bound ^ (rule.network.sourceIncidentEdges.card ^ extra))
      (pow_le_one₀ hbound0 hbound1) ih state
    simpa only [Nat.add_succ, pow_succ, pow_mul] using hstep

end
end Universality.Rule
