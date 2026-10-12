import IGSIII34.Resistance.IntegrationByParts

set_option autoImplicit false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

/-- An explicitly constructed Kirchhoff flow and Ohmic potential identify
the actual Thomson resistance. This provides the reduction interface for
the finite series/parallel density family, without assuming a response law. -/
theorem effectiveResistance_eq_ohmic_voltage
    (network : FiniteNetwork Vertex Edge)
    (resistance current : Edge → ℝ) (potential : Vertex → ℝ)
    (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (ohm : ∀ edge, resistance edge * current edge =
      potential (network.endpoint edge).1 - potential (network.endpoint edge).2) :
    network.effectiveResistance resistance = potential network.source - potential network.target := by
  have voltage := network.unitFlow_energy_eq_voltage unitFlow ohm
  apply le_antisymm
  · exact (network.effectiveResistance_le_energy nonnegative unitFlow).trans_eq voltage
  · apply network.le_effectiveResistance ⟨current, unitFlow⟩ resistance
    intro trial trialUnitFlow
    have cross : crossEnergy resistance current trial = potential network.source - potential network.target := by
      rw [← network.unitFlow_integrationByParts trialUnitFlow potential]
      apply Finset.sum_congr rfl
      intro edge _
      rw [← ohm]
      ring
    have squareNonnegative := energy_nonneg nonnegative (fun edge => trial edge - current edge)
    have identity : energy resistance (fun edge => trial edge - current edge) =
        energy resistance trial + energy resistance current - 2 * crossEnergy resistance current trial := by
      simp only [energy, crossEnergy]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro edge _
      ring
    rw [identity, cross, voltage] at squareNonnegative
    linarith

end
end IGSIII34.Resistance.FiniteNetwork
