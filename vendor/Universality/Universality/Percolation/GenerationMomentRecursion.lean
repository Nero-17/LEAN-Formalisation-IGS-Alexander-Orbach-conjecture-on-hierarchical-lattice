import Universality.Graph.GenerationReassociation

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

/-- The top-level recursion for actual moments on the pre-existing finite
generation, justified by a terminal- and edge-preserving graph equivalence. -/
theorem generation_conditionalInternalMoment (rule : Rule) (p : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (n r : ℕ) (opened sourceSelected targetSelected : Bool) :
    (rule.generation (n + 1)).network.conditionalInternalMoment p opened sourceSelected targetSelected r =
      ∑ coarse, rule.network.conditionalCellWeight p opened coarse *
        ∑ k ∈ Finset.range (r + 1),
          (rule.network.internalSelectedMass sourceSelected targetSelected coarse : ℝ) ^ (r - k) *
            (r.choose k : ℝ) *
          ∑ assignment : Fin k → Fin rule.edges, ∏ edge,
            (rule.generation n).network.conditionalInternalMoment p (coarse edge)
              (rule.network.orientedChildState sourceSelected targetSelected coarse edge).sourceSelected
              (rule.network.orientedChildState sourceSelected targetSelected coarse edge).targetSelected
              (Fintype.card {a : Fin k // assignment a = edge}) := by
  rw [← (rule.generationTopDecomposition n).conditionalInternalMoment]
  rw [rule.network.conditionalInternalMoment_substitute (rule.generation n).network p
    (by rwa [rule.generation_fixed_point p hfixed n])
    (by rwa [rule.generation_fixed_point p hfixed n]), rule.generation_fixed_point p hfixed n]

end
end Universality.Rule
