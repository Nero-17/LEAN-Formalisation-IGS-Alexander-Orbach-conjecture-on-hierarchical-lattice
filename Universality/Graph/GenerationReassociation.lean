import Universality.Graph.SubstitutionEquivalence
import Universality.Graph.SubstitutionAssociativity
import Universality.Graph.Iteration

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- The existing bottom-up finite generation is equivalent to one rule with
the previous generation placed inside every edge. -/
def generationTopDecomposition (rule : Rule) : (n : ℕ) →
    (rule.generation (n + 1)).network.NetworkEquivalence
      (rule.network.substitute (rule.generation n).network)
  | 0 => NetworkEquivalence.refl _
  | n + 1 =>
    ((generationTopDecomposition rule n).substitute (NetworkEquivalence.refl rule.network)).trans
      (rule.network.substitutionAssociativity (rule.generation n).network rule.network)

end
end Universality.Rule
