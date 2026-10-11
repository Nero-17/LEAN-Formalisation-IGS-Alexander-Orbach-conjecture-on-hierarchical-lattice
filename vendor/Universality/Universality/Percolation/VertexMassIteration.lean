import Universality.Percolation.VertexMassResponse
import Universality.Graph.Iteration

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix

/-- Internal vertex expectations in a finite generation are an affine matrix
sum, rather than the edge-cluster matrix power from Section 2. -/
theorem generation_conditionalVertexMass (rule : Rule) (p : ℝ)
    (hfixed : rule.network.reliability p = p) (hp : 0 < p) (hp' : p < 1)
    (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source)
    (n : ℕ) (σ : LiveState) :
    (rule.generation n).network.conditionalVertexMass p σ =
      ∑ k ∈ Finset.range (n + 1),
        (rule.network.massMatrix p ^ k *ᵥ rule.network.conditionalVertexMass p) σ := by
  induction n with
  | zero => simp [generation]
  | succ n ih =>
    conv_rhs => rw [Finset.sum_range_succ]
    change ((rule.generation n).network.substitute rule.network).conditionalVertexMass p σ = _
    rw [FiniteNetwork.conditionalVertexMass_substitute _ _ p
      (by rwa [hfixed]) (by rwa [hfixed]) symmetry hs ht, hfixed,
      rule.generation_massMatrix p hfixed hp hp' symmetry hs ht, ih]

end
end Universality.Rule
