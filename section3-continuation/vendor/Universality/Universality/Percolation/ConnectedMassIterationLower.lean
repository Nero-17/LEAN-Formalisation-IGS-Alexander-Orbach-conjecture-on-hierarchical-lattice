import Universality.Percolation.MassMeanEquivalence
import Universality.Percolation.AllOpenMassLower
import Universality.Percolation.OffcriticalMomentRecursion
import Universality.Percolation.VertexMassPositivity
import Universality.Percolation.SupercriticalFailureSummability

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 0

theorem Classical.generation_connected_mass_allOpen_lower {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (n : ℕ) :
    (rule.edges : ℝ) * (rule.generation n).network.reliability p ^ rule.edges *
      (rule.generation n).network.conditionalVertexMass p .connected ≤
      (rule.generation (n + 1)).network.reliability p *
        (rule.generation (n + 1)).network.conditionalVertexMass p .connected := by
  have hpositive := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr
    ((h.generation n).connected _)
  have hless := (rule.generation n).network.reliability_lt_one hp hp'
  have hnonnegative (state : LiveState) : 0 ≤ (rule.generation n).network.conditionalVertexMass p state :=
    (rule.generation n).network.conditionalInternalMean_nonneg p hp.le hp'.le _ _ _
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  have hmean : (rule.generation (n + 1)).network.conditionalVertexMass p .connected =
      rule.network.conditionalVertexMass ((rule.generation n).network.reliability p) .connected +
        (rule.network.massMatrix ((rule.generation n).network.reliability p) *ᵥ
          (rule.generation n).network.conditionalVertexMass p) .connected := by
    unfold conditionalVertexMass
    rw [← (rule.generationTopDecomposition n).conditionalInternalMean]
    exact rule.network.conditionalVertexMass_substitute (rule.generation n).network p hpositive hless symmetry hs ht .connected
  have hcross : (rule.generation (n + 1)).network.reliability p =
      rule.network.reliability ((rule.generation n).network.reliability p) := by
    rw [← (rule.generationTopDecomposition n).reliability, substitute_reliability]
  rw [hmean, hcross]
  have hresponse := rule.network.connected_response_allOpen_lower h.connected
    ((rule.generation n).network.reliability p) hpositive hless
    ((rule.generation n).network.conditionalVertexMass p) hnonnegative
  have hreward := rule.network.conditionalInternalMean_nonneg
    ((rule.generation n).network.reliability p) hpositive.le hless.le true true false
  have hq := (rule.network.reliability_pos_iff_connected hpositive hless).mpr (h.connected _)
  change 0 ≤ rule.network.conditionalVertexMass ((rule.generation n).network.reliability p) .connected at hreward
  nlinarith [mul_nonneg hq.le hreward]

end
end Universality.Rule
