import IGSIII34.Resistance.Nonnegative
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem effectiveResistance_lipschitzOn_nonnegative (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    LipschitzOnWith (Fintype.card Edge : NNReal) network.effectiveResistance
      {resistance | ∀ edge, 0 ≤ resistance edge} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first firstNonnegative second secondNonnegative
  rw [Real.dist_eq]
  calc
    _ ≤ ∑ edge, |first edge - second edge| :=
      network.effectiveResistance_abs_sub_le_sum_abs_of_nonnegative connected
        firstNonnegative secondNonnegative
    _ ≤ ∑ _edge : Edge, dist first second := by
      apply Finset.sum_le_sum
      intro edge _
      simpa only [Real.dist_eq] using dist_le_pi_dist first second edge
    _ = _ := by simp [nsmul_eq_mul]

theorem effectiveResistance_continuousOn_nonnegative (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    ContinuousOn network.effectiveResistance {resistance | ∀ edge, 0 ≤ resistance edge} :=
  (network.effectiveResistance_lipschitzOn_nonnegative connected).continuousOn

theorem effectiveResistance_weighted_sum_lower_bound
    {Index : Type*} [Fintype Index] (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) (weight : Index → ℝ)
    (weightNonnegative : ∀ index, 0 ≤ weight index) (resistance : Index → Edge → ℝ)
    (resistanceNonnegative : ∀ index edge, 0 ≤ resistance index edge) :
    ∑ index, weight index * network.effectiveResistance (resistance index) ≤
      network.effectiveResistance (fun edge => ∑ index, weight index * resistance index edge) := by
  apply network.le_effectiveResistance feasible
  intro current unitFlow
  calc
    _ ≤ ∑ index, weight index * energy (resistance index) current := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul_of_nonneg_left
        (network.effectiveResistance_le_energy (resistanceNonnegative index) unitFlow)
        (weightNonnegative index)
    _ = energy (fun edge => ∑ index, weight index * resistance index edge) current := by
      simp only [energy, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

end
end IGSIII34.Resistance.FiniteNetwork
