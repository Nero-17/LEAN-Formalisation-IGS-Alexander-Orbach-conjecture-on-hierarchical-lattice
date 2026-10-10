import IGSIII34.Resistance.ZeroResistance
import IGSIII34.Percolation.SmallConfiguration
import IGSIII34.Percolation.LawMap

set_option autoImplicit false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork Resistance.FiniteNetwork

theorem electricalCell_zeroConfiguration_crosses {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crosses : rule.crosses configuration = true)
    {input : Fin edges → ℝ} (nonnegative : ∀ edge, 0 ≤ input edge)
    (resistanceZero : electricalCell rule configuration input = 0) :
    rule.crosses (smallConfiguration configuration input 0) = true := by
  have reachable := (network rule configuration).zeroEdgeGraph_connected_of_zero_resistance
    (connected_of_crosses _ _ crosses) (fun edge => nonnegative edge.val) resistanceZero
  rw [smallEdgeGraph_eq_openGraph] at reachable
  exact (rule.crosses_eq_true _).mpr reachable

end
end IGSIII34.Percolation
