import IGSIII34.Resistance.DirichletTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem reachable_of_unitFlow (network : FiniteNetwork Vertex Edge)
    {current : Edge → ℝ} (unitFlow : current ∈ network.unitFlows) :
    network.graph.Reachable network.source network.target := by
  by_contra disconnected
  obtain ⟨potential, atSource, atTarget, energyZero⟩ :=
    network.exists_zero_energy_boundaryPotential_of_disconnected disconnected (fun _ => 1) 1 0
  have contradiction := network.weighted_cauchy_schwarz (resistance := fun _ => 1)
    (fun _ => by norm_num) current potential
  rw [network.unitFlow_integrationByParts unitFlow, atSource, atTarget, energyZero] at contradiction
  norm_num at contradiction

theorem unitFlows_nonempty_iff_reachable (network : FiniteNetwork Vertex Edge) :
    network.unitFlows.Nonempty ↔ network.graph.Reachable network.source network.target :=
  ⟨fun ⟨_, unitFlow⟩ => network.reachable_of_unitFlow unitFlow,
    fun reachable => network.unitFlows_nonempty_of_connected reachable⟩

theorem disconnected_effectiveResistance (network : FiniteNetwork Vertex Edge)
    (disconnected : ¬ network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) : network.effectiveResistance resistance = 0 := by
  have empty : network.unitFlows = ∅ := by
    ext current
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun unitFlow => disconnected (network.reachable_of_unitFlow unitFlow)
  simp only [effectiveResistance, flowEnergies, empty, Set.image_empty, Real.sInf_empty]

end
end IGSIII34.Resistance.FiniteNetwork
