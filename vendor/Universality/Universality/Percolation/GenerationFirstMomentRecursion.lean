import Universality.Percolation.MassMeanEquivalence
import Universality.Percolation.OffcriticalMomentRecursion
import Universality.Percolation.VertexMassResponse

namespace Universality.Rule
noncomputable section
open FiniteNetwork

theorem Classical.generation_conditionalVertexMass_offcritical {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (n : ℕ) (state : LiveState) :
    (rule.generation (n + 1)).network.conditionalVertexMass p state =
      rule.network.conditionalVertexMass ((rule.generation n).network.reliability p) state +
        ∑ child, rule.network.massMatrix ((rule.generation n).network.reliability p) state child *
          (rule.generation n).network.conditionalVertexMass p child := by
  have hpositive := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr
    ((h.generation n).connected _)
  have hless := (rule.generation n).network.reliability_lt_one hp hp'
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  unfold conditionalVertexMass
  rw [← (rule.generationTopDecomposition n).conditionalInternalMean]
  exact rule.network.conditionalVertexMass_substitute (rule.generation n).network p hpositive hless symmetry hs ht state

end
end Universality.Rule
