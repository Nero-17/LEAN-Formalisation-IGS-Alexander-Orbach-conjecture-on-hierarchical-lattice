import Universality.Graph.ConductanceMultiplicativity
import Universality.Examples.TieGemClassical

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork

theorem twoEdgePath_unitConductance : twoEdgePathNetwork.unitConductance = (1/2 : ℝ) := by
  apply le_antisymm
  · have hh := twoEdgePathNetwork.unitConductance_le_energy ![(1 : ℝ), 0, 1/2] (by rfl) (by rfl)
    norm_num [dirichletEnergy, twoEdgePathNetwork, Fin.sum_univ_succ, Matrix.cons_val_two] at hh
    exact hh
  · apply twoEdgePathNetwork.le_unitConductance
    intro potential hs ht
    change potential 0 = 1 at hs
    change potential 1 = 0 at ht
    norm_num [dirichletEnergy, twoEdgePathNetwork, Fin.sum_univ_succ, hs, ht]
    nlinarith [sq_nonneg (potential 2 - 1/2)]

theorem triangle_unitConductance : triangleNetwork.unitConductance = (3/2 : ℝ) := by
  apply le_antisymm
  · have hh := triangleNetwork.unitConductance_le_energy ![(1 : ℝ), 0, 1/2] (by rfl) (by rfl)
    norm_num [dirichletEnergy, triangleNetwork, Fin.sum_univ_succ, Matrix.cons_val_two] at hh
    exact hh
  · apply triangleNetwork.le_unitConductance
    intro potential hs ht
    change potential 0 = 1 at hs
    change potential 1 = 0 at ht
    norm_num [dirichletEnergy, triangleNetwork, Fin.sum_univ_succ, hs, ht]
    nlinarith [sq_nonneg (potential 2 - 1/2)]

theorem tie_gem_unitConductance : tieRule.network.unitConductance = (3/4 : ℝ) ∧
    gemRule.network.unitConductance = (3/4 : ℝ) := by
  constructor
  · change (twoEdgePathNetwork.substitute triangleNetwork).unitConductance = _
    rw [substitute_unitConductance, twoEdgePath_unitConductance, triangle_unitConductance]
    norm_num
  · change (triangleNetwork.substitute twoEdgePathNetwork).unitConductance = _
    rw [substitute_unitConductance, triangle_unitConductance, twoEdgePath_unitConductance]
    norm_num

theorem tie_gem_unitEffectiveResistance
    (htie : tieRule.network.fullGraph.Reachable tieRule.network.source tieRule.network.target)
    (hgem : gemRule.network.fullGraph.Reachable gemRule.network.source gemRule.network.target) :
    tieRule.network.unitEffectiveResistance htie = (4/3 : ℝ) ∧
      gemRule.network.unitEffectiveResistance hgem = (4/3 : ℝ) := by
  simp only [unitEffectiveResistance, tie_gem_unitConductance.1, tie_gem_unitConductance.2]
  norm_num

end
end Universality
