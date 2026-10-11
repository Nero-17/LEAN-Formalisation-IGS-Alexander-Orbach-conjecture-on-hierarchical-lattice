import IGSIII34.Percolation.ClassicalStrict
import IGSIII.Chemical.TransferOperator

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution

theorem shortest_eq_indexed_weightedDistance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (input : Fin edges → ℝ) :
    (edgePathFamily network configuration).shortest input =
      weightedDistance (network.openGraph configuration) (indexedResistanceCost network input)
        network.source network.target := by
  simpa only [indexedResistanceCost_at_endpoint network simple input] using
    edgePathFamily_shortest_eq_weightedDistance network simple configuration (indexedResistanceCost network input)

theorem electricalCell_le_shortest {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (input : Fin edges → ℝ) (nonnegative : ∀ edge, 0 ≤ input edge) :
    electricalCell network configuration input ≤ (edgePathFamily network configuration).shortest input := by
  rw [shortest_eq_indexed_weightedDistance network simple configuration input]
  exact electricalCell_le_chemical_cost network simple configuration crossing input nonnegative

theorem classical_allOpen_resistance_lt_shortest (rule : Rule) (classicalRule : rule.Classical)
    (input : Fin rule.edges → ℝ) (positive : ∀ edge, 0 < input edge) :
    electricalCell rule.network (fun _ => true) input <
      (edgePathFamily rule.network (fun _ => true)).shortest input := by
  rw [shortest_eq_indexed_weightedDistance rule.network classicalRule.simple (fun _ => true) input]
  exact classical_allOpen_resistance_strict rule classicalRule input positive

end
end IGSIII4
