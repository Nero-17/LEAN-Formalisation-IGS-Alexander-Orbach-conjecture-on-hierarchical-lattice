import IGSIII34.Resistance.Dirichlet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def boundaryPotentialEnergies (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (sourceValue targetValue : ℝ) : Set ℝ :=
  {value | ∃ potential : Vertex → ℝ, potential network.source = sourceValue ∧
    potential network.target = targetValue ∧ network.potentialEnergy resistance potential = value}

theorem boundaryPotentialEnergies_nonempty (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (sourceValue targetValue : ℝ) :
    (network.boundaryPotentialEnergies resistance sourceValue targetValue).Nonempty := by
  let potential : Vertex → ℝ := fun vertex => if vertex = network.source then sourceValue else targetValue
  refine ⟨network.potentialEnergy resistance potential, potential, ?_, ?_, rfl⟩
  · simp [potential]
  · simp [potential, network.distinct.symm]

theorem boundaryPotential_energy_lower_bound (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (potential : Vertex → ℝ) :
    (potential network.source - potential network.target) ^ 2 / network.effectiveResistance resistance ≤
      network.potentialEnergy resistance potential := by
  obtain ⟨current, unitFlow, minimal⟩ := network.exists_minimizing_unitFlow_of_connected connected positive
  have cauchy := network.weighted_cauchy_schwarz positive current potential
  rw [network.unitFlow_integrationByParts unitFlow, minimal] at cauchy
  apply (div_le_iff₀ (network.effectiveResistance_pos_of_connected connected positive)).mpr
  simpa only [mul_comm] using cauchy

theorem exists_boundaryPotential_minimizer (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (sourceValue targetValue : ℝ) :
    ∃ potential : Vertex → ℝ, potential network.source = sourceValue ∧
      potential network.target = targetValue ∧ network.potentialEnergy resistance potential =
        (sourceValue - targetValue) ^ 2 / network.effectiveResistance resistance := by
  obtain ⟨current, unitFlow, minimal⟩ := network.exists_minimizing_unitFlow_of_connected connected positive
  obtain ⟨potential, ohm⟩ := network.minimizing_current_has_potential positive unitFlow minimal
  have voltageIdentity := network.unitFlow_energy_eq_voltage unitFlow ohm
  have resistancePositive := network.effectiveResistance_pos_of_connected connected positive
  let boundaryPotential : Vertex → ℝ := fun vertex => targetValue +
    (sourceValue - targetValue) * (potential vertex - potential network.target) /
      network.effectiveResistance resistance
  have atSource : boundaryPotential network.source = sourceValue := by
    dsimp [boundaryPotential]
    rw [← voltageIdentity, minimal]
    field_simp [resistancePositive.ne']
    ring
  have atTarget : boundaryPotential network.target = targetValue := by simp [boundaryPotential]
  have potentialDifference (edge : Edge) :
      boundaryPotential (network.endpoint edge).1 - boundaryPotential (network.endpoint edge).2 =
        (sourceValue - targetValue) * (resistance edge * current edge) /
          network.effectiveResistance resistance := by
    dsimp [boundaryPotential]
    rw [ohm]
    ring
  refine ⟨boundaryPotential, atSource, atTarget, ?_⟩
  unfold potentialEnergy
  simp_rw [potentialDifference]
  calc
    _ = ∑ edge, ((sourceValue - targetValue) ^ 2 / network.effectiveResistance resistance ^ 2) *
        (resistance edge * current edge ^ 2) := by
      apply Finset.sum_congr rfl
      intro edge _
      field_simp [resistancePositive.ne', (positive edge).ne']
    _ = ((sourceValue - targetValue) ^ 2 / network.effectiveResistance resistance ^ 2) *
        energy resistance current := by rw [energy, Finset.mul_sum]
    _ = _ := by
      rw [minimal]
      field_simp [resistancePositive.ne']

theorem boundaryPotential_trace (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (sourceValue targetValue : ℝ) :
    sInf (network.boundaryPotentialEnergies resistance sourceValue targetValue) =
      (sourceValue - targetValue) ^ 2 / network.effectiveResistance resistance := by
  obtain ⟨potential, atSource, atTarget, minimizing⟩ :=
    network.exists_boundaryPotential_minimizer connected positive sourceValue targetValue
  have nonnegative : BddBelow (network.boundaryPotentialEnergies resistance sourceValue targetValue) := by
    refine ⟨0, ?_⟩
    rintro value ⟨competitor, _, _, rfl⟩
    exact network.potentialEnergy_nonnegative positive competitor
  apply le_antisymm
  · exact csInf_le nonnegative ⟨potential, atSource, atTarget, minimizing⟩
  · apply le_csInf (network.boundaryPotentialEnergies_nonempty resistance sourceValue targetValue)
    rintro value ⟨competitor, atSource, atTarget, rfl⟩
    simpa only [atSource, atTarget] using network.boundaryPotential_energy_lower_bound connected positive competitor

theorem exists_zero_energy_boundaryPotential_of_disconnected (network : FiniteNetwork Vertex Edge)
    (disconnected : ¬ network.graph.Reachable network.source network.target)
    (resistance : Edge → ℝ) (sourceValue targetValue : ℝ) :
    ∃ potential : Vertex → ℝ, potential network.source = sourceValue ∧
      potential network.target = targetValue ∧ network.potentialEnergy resistance potential = 0 := by
  classical
  let potential : Vertex → ℝ := fun vertex =>
    if network.graph.Reachable network.source vertex then sourceValue else targetValue
  refine ⟨potential, by simp [potential], by simp [potential, disconnected], ?_⟩
  have equalAcrossEdge (edge : Edge) :
      potential (network.endpoint edge).1 = potential (network.endpoint edge).2 := by
    by_cases same : (network.endpoint edge).1 = (network.endpoint edge).2
    · rw [same]
    · have adjacent : network.graph.Adj (network.endpoint edge).1 (network.endpoint edge).2 :=
        ⟨same, edge, Or.inl rfl⟩
      have reachabilityEquivalent : network.graph.Reachable network.source (network.endpoint edge).1 ↔
          network.graph.Reachable network.source (network.endpoint edge).2 :=
        ⟨fun reachable => reachable.trans adjacent.reachable,
          fun reachable => reachable.trans adjacent.symm.reachable⟩
      simp only [potential, reachabilityEquivalent]
  simp only [potentialEnergy, equalAcrossEdge, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div,
    Finset.sum_const_zero]

theorem disconnected_boundaryPotential_trace (network : FiniteNetwork Vertex Edge)
    (disconnected : ¬ network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (sourceValue targetValue : ℝ) :
    sInf (network.boundaryPotentialEnergies resistance sourceValue targetValue) = 0 := by
  obtain ⟨potential, atSource, atTarget, zeroEnergy⟩ :=
    network.exists_zero_energy_boundaryPotential_of_disconnected disconnected resistance sourceValue targetValue
  have nonnegative : BddBelow (network.boundaryPotentialEnergies resistance sourceValue targetValue) := by
    refine ⟨0, ?_⟩
    rintro value ⟨competitor, _, _, rfl⟩
    exact network.potentialEnergy_nonnegative positive competitor
  apply le_antisymm
  · exact csInf_le nonnegative ⟨potential, atSource, atTarget, zeroEnergy⟩
  · apply le_csInf (network.boundaryPotentialEnergies_nonempty resistance sourceValue targetValue)
    rintro value ⟨competitor, _, _, rfl⟩
    exact network.potentialEnergy_nonnegative positive competitor

end
end IGSIII34.Resistance.FiniteNetwork
