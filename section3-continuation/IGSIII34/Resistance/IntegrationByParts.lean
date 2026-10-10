import IGSIII34.Resistance.Potential

/-! Discrete integration by parts and the voltage drop of a unit electrical flow. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem sum_potential_mul_divergence (network : FiniteNetwork Vertex Edge)
    (current : Edge → ℝ) (potential : Vertex → ℝ) :
    ∑ vertex, potential vertex * network.divergence current vertex =
      ∑ edge, current edge *
        (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) := by
  simp only [divergence, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp [eq_comm, mul_comm]

theorem unitFlow_integrationByParts (network : FiniteNetwork Vertex Edge)
    {current : Edge → ℝ} (unitFlow : current ∈ network.unitFlows)
    (potential : Vertex → ℝ) :
    ∑ edge, current edge *
        (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) =
      potential network.source - potential network.target := by
  rw [← network.sum_potential_mul_divergence]
  have divergenceIdentity (vertex : Vertex) : network.divergence current vertex =
      (if vertex = network.source then 1 else 0) -
        (if vertex = network.target then 1 else 0) := unitFlow vertex
  simp_rw [divergenceIdentity]
  simp [mul_sub, Finset.sum_sub_distrib]

theorem unitFlow_energy_eq_voltage (network : FiniteNetwork Vertex Edge)
    {current resistance : Edge → ℝ} {potential : Vertex → ℝ}
    (unitFlow : current ∈ network.unitFlows)
    (ohm : ∀ edge, resistance edge * current edge =
      potential (network.endpoint edge).1 - potential (network.endpoint edge).2) :
    energy resistance current = potential network.source - potential network.target := by
  rw [← network.unitFlow_integrationByParts unitFlow potential]
  apply Finset.sum_congr rfl
  intro edge _
  rw [← ohm]
  ring

end
end IGSIII34.Resistance.FiniteNetwork
