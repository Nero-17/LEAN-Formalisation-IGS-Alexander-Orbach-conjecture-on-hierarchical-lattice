import IGSIII34.Resistance.IntegrationByParts
import Mathlib.Tactic.FieldSimp

/-!
# Weighted Dirichlet conductance and Thomson duality

Both variational functionals are defined from the same finite network. The
duality proof uses the constructed minimizing unit flow and potential, together
with weighted Cauchy--Schwarz and discrete integration by parts.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def potentialEnergy (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (potential : Vertex → ℝ) : ℝ :=
  ∑ edge, (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 /
    resistance edge

def unitPotentialEnergies (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) : Set ℝ :=
  {value | ∃ potential : Vertex → ℝ, potential network.source = 1 ∧
    potential network.target = 0 ∧ network.potentialEnergy resistance potential = value}

def effectiveConductance (network : FiniteNetwork Vertex Edge) (resistance : Edge → ℝ) : ℝ :=
  sInf (network.unitPotentialEnergies resistance)

theorem potentialEnergy_nonnegative (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (potential : Vertex → ℝ) : 0 ≤ network.potentialEnergy resistance potential :=
  Finset.sum_nonneg (fun edge _ => div_nonneg (sq_nonneg _) (positive edge).le)

theorem unitPotentialEnergies_nonempty (network : FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) : (network.unitPotentialEnergies resistance).Nonempty := by
  let potential : Vertex → ℝ := fun vertex => if vertex = network.source then 1 else 0
  refine ⟨network.potentialEnergy resistance potential, potential, ?_, ?_, rfl⟩
  · simp [potential]
  · simp [potential, network.distinct.symm]

theorem unitPotentialEnergies_bddBelow (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    BddBelow (network.unitPotentialEnergies resistance) := by
  refine ⟨0, ?_⟩
  rintro value ⟨potential, _, _, rfl⟩
  exact network.potentialEnergy_nonnegative positive potential

theorem effectiveConductance_le_energy (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    {potential : Vertex → ℝ} (sourceValue : potential network.source = 1)
    (targetValue : potential network.target = 0) :
    network.effectiveConductance resistance ≤ network.potentialEnergy resistance potential :=
  csInf_le (network.unitPotentialEnergies_bddBelow positive) ⟨potential, sourceValue, targetValue, rfl⟩

theorem weighted_cauchy_schwarz (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (current : Edge → ℝ) (potential : Vertex → ℝ) :
    (∑ edge, current edge *
      (potential (network.endpoint edge).1 - potential (network.endpoint edge).2)) ^ 2 ≤
        energy resistance current * network.potentialEnergy resistance potential := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun edge => Real.sqrt (resistance edge) * current edge)
    (fun edge => (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) /
      Real.sqrt (resistance edge))
  have productIdentity (edge : Edge) :
      (Real.sqrt (resistance edge) * current edge) *
          ((potential (network.endpoint edge).1 - potential (network.endpoint edge).2) /
            Real.sqrt (resistance edge)) =
        current edge * (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (positive edge))]
  have currentSquare (edge : Edge) : (Real.sqrt (resistance edge) * current edge) ^ 2 =
      resistance edge * current edge ^ 2 := by rw [mul_pow, Real.sq_sqrt (positive edge).le]
  have potentialSquare (edge : Edge) :
      ((potential (network.endpoint edge).1 - potential (network.endpoint edge).2) /
          Real.sqrt (resistance edge)) ^ 2 =
        (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 /
          resistance edge := by rw [div_pow, Real.sq_sqrt (positive edge).le]
  simpa only [productIdentity, currentSquare, potentialSquare, energy, potentialEnergy] using cauchy

theorem reciprocalResistance_le_conductance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    1 / network.effectiveResistance resistance ≤ network.effectiveConductance resistance := by
  obtain ⟨current, unitFlow, minimal⟩ :=
    network.exists_minimizing_unitFlow_of_connected connected positive
  have resistancePositive := network.effectiveResistance_pos_of_connected connected positive
  apply le_csInf (network.unitPotentialEnergies_nonempty resistance)
  rintro value ⟨potential, sourceValue, targetValue, rfl⟩
  apply (div_le_iff₀ resistancePositive).mpr
  have cauchy := network.weighted_cauchy_schwarz positive current potential
  rw [network.unitFlow_integrationByParts unitFlow, sourceValue, targetValue, minimal] at cauchy
  norm_num only [sub_zero, one_pow] at cauchy
  nlinarith

theorem effectiveConductance_eq_reciprocalResistance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    network.effectiveConductance resistance = 1 / network.effectiveResistance resistance := by
  obtain ⟨current, unitFlow, minimal⟩ :=
    network.exists_minimizing_unitFlow_of_connected connected positive
  obtain ⟨potential, ohm⟩ := network.minimizing_current_has_potential positive unitFlow minimal
  have voltage := network.unitFlow_energy_eq_voltage unitFlow ohm
  have resistancePositive := network.effectiveResistance_pos_of_connected connected positive
  let normalizedPotential : Vertex → ℝ := fun vertex =>
    (potential vertex - potential network.target) / network.effectiveResistance resistance
  have sourceValue : normalizedPotential network.source = 1 := by
    dsimp [normalizedPotential]
    rw [← voltage, minimal]
    exact div_self (ne_of_gt resistancePositive)
  have targetValue : normalizedPotential network.target = 0 := by simp [normalizedPotential]
  have potentialDifference (edge : Edge) :
      normalizedPotential (network.endpoint edge).1 - normalizedPotential (network.endpoint edge).2 =
        resistance edge * current edge / network.effectiveResistance resistance := by
    dsimp [normalizedPotential]
    rw [ohm]
    ring
  have normalizedEnergy : network.potentialEnergy resistance normalizedPotential =
      1 / network.effectiveResistance resistance := by
    unfold potentialEnergy
    simp_rw [potentialDifference]
    calc
      ∑ edge, (resistance edge * current edge / network.effectiveResistance resistance) ^ 2 /
          resistance edge =
        ∑ edge, resistance edge * current edge ^ 2 / network.effectiveResistance resistance ^ 2 := by
          apply Finset.sum_congr rfl
          intro edge _
          field_simp [ne_of_gt (positive edge), ne_of_gt resistancePositive]
      _ = energy resistance current / network.effectiveResistance resistance ^ 2 := by
        simp only [energy, div_eq_mul_inv, Finset.sum_mul]
      _ = 1 / network.effectiveResistance resistance := by
        rw [minimal]
        field_simp
  apply le_antisymm
  · exact (network.effectiveConductance_le_energy positive sourceValue targetValue).trans_eq normalizedEnergy
  · exact network.reciprocalResistance_le_conductance connected positive

theorem effectiveResistance_eq_inverseConductance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    network.effectiveResistance resistance = (network.effectiveConductance resistance)⁻¹ := by
  rw [network.effectiveConductance_eq_reciprocalResistance connected positive, one_div, inv_inv]

end
end IGSIII34.Resistance.FiniteNetwork
