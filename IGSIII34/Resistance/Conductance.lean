import IGSIII34.Resistance.Dirichlet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def conductanceEnergy (network : FiniteNetwork Vertex Edge)
    (conductance : Edge → ℝ) (potential : Vertex → ℝ) : ℝ :=
  ∑ edge, conductance edge *
    (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2

def conductanceEnergies (network : FiniteNetwork Vertex Edge)
    (conductance : Edge → ℝ) : Set ℝ :=
  {value | ∃ potential : Vertex → ℝ, potential network.source = 1 ∧
    potential network.target = 0 ∧ network.conductanceEnergy conductance potential = value}

def conductanceFunctional (network : FiniteNetwork Vertex Edge) (conductance : Edge → ℝ) : ℝ :=
  sInf (network.conductanceEnergies conductance)

theorem conductanceEnergies_nonempty (network : FiniteNetwork Vertex Edge)
    (conductance : Edge → ℝ) : (network.conductanceEnergies conductance).Nonempty := by
  let potential : Vertex → ℝ := fun vertex => if vertex = network.source then 1 else 0
  refine ⟨network.conductanceEnergy conductance potential, potential, ?_, ?_, rfl⟩
  · simp [potential]
  · simp [potential, network.distinct.symm]

theorem conductanceEnergies_bddBelow (network : FiniteNetwork Vertex Edge)
    {conductance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ conductance edge) :
    BddBelow (network.conductanceEnergies conductance) := by
  refine ⟨0, ?_⟩
  rintro value ⟨potential, _, _, rfl⟩
  exact Finset.sum_nonneg (fun edge _ => mul_nonneg (nonnegative edge) (sq_nonneg _))

theorem conductanceFunctional_le_energy (network : FiniteNetwork Vertex Edge)
    {conductance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ conductance edge)
    {potential : Vertex → ℝ} (sourceValue : potential network.source = 1)
    (targetValue : potential network.target = 0) :
    network.conductanceFunctional conductance ≤ network.conductanceEnergy conductance potential :=
  csInf_le (network.conductanceEnergies_bddBelow nonnegative)
    ⟨potential, sourceValue, targetValue, rfl⟩

theorem conductanceFunctional_weighted_sum_lower_bound
    {Index : Type*} [Fintype Index] (network : FiniteNetwork Vertex Edge)
    (weight : Index → ℝ) (weightNonnegative : ∀ index, 0 ≤ weight index)
    (conductance : Index → Edge → ℝ)
    (conductanceNonnegative : ∀ index edge, 0 ≤ conductance index edge) :
    ∑ index, weight index * network.conductanceFunctional (conductance index) ≤
      network.conductanceFunctional (fun edge => ∑ index, weight index * conductance index edge) := by
  apply le_csInf (network.conductanceEnergies_nonempty _)
  rintro value ⟨potential, sourceValue, targetValue, rfl⟩
  calc
    _ ≤ ∑ index, weight index * network.conductanceEnergy (conductance index) potential := by
      apply Finset.sum_le_sum
      intro index _
      exact mul_le_mul_of_nonneg_left
        (network.conductanceFunctional_le_energy (conductanceNonnegative index) sourceValue targetValue)
        (weightNonnegative index)
    _ = _ := by
      simp only [conductanceEnergy, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

theorem conductanceFunctional_eq_effectiveConductance (network : FiniteNetwork Vertex Edge)
    (conductance : Edge → ℝ) :
    network.conductanceFunctional conductance =
      network.effectiveConductance (fun edge => (conductance edge)⁻¹) := by
  have energyIdentity (potential : Vertex → ℝ) :
      network.conductanceEnergy conductance potential =
        network.potentialEnergy (fun edge => (conductance edge)⁻¹) potential := by
    simp only [conductanceEnergy, potentialEnergy, div_inv_eq_mul, mul_comm]
  simp only [conductanceFunctional, effectiveConductance, conductanceEnergies,
    unitPotentialEnergies, energyIdentity]

theorem conductanceFunctional_eq_reciprocalResistance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {conductance : Edge → ℝ} (positive : ∀ edge, 0 < conductance edge) :
    network.conductanceFunctional conductance =
      1 / network.effectiveResistance (fun edge => (conductance edge)⁻¹) := by
  rw [network.conductanceFunctional_eq_effectiveConductance]
  exact network.effectiveConductance_eq_reciprocalResistance connected
    (fun edge => inv_pos.mpr (positive edge))

end
end IGSIII34.Resistance.FiniteNetwork
