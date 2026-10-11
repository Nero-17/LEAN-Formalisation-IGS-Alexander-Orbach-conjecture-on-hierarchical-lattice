import IGSIII34.ResistanceLimit.CellPreservedEnergy
import IGSIII34.ResistanceLimit.ElectricalRadius

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- A crossing cell cannot collapse under its actual ambient electrical
embedding. The explicit factor depends only on its terminal resistance and
the finite coarse-boundary trace, so it survives compatible refinement. -/
theorem substituted_cell_resistance_lower_bound
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (chosen : Fin outerEdges)
    (crossing : inner.crosses (configuration chosen) = true)
    (first last : Fin innerVertices) (reachable : (inner.openGraph (configuration chosen)).Reachable first last) :
    pairResistance (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩) first last ≤
      (1 + cellBoundaryTestEnergy outer inner configuration resistance chosen *
        (network inner (configuration chosen)).effectiveResistance (fun child => resistance ⟨chosen, child⟩)) *
      pairResistance (substitutedNetwork outer inner configuration) resistance
        (outer.cellVertex inner chosen first) (outer.cellVertex inner chosen last) := by
  by_cases distinct : first ≠ last
  · have childReach : (network inner (configuration chosen)).graph.Reachable first last := by
      rw [graph_eq_openGraph]
      exact reachable
    let vertices : Fin innerVertices ↪ outer.SubstitutionVertex inner :=
      ⟨outer.cellVertex inner chosen, outer.cellVertex_injective inner chosen⟩
    let edges : {child : Fin innerEdges // configuration chosen child = true} ↪
        (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) :=
      ⟨fun child => ⟨chosen, child⟩, by intro first last equal; cases equal; rfl⟩
    have parentReach := childReach.map (networkEmbeddingGraphHom
      (network inner (configuration chosen)) (substitutedNetwork outer inner configuration)
      vertices edges (fun _ => rfl))
    have parentDistinct : outer.cellVertex inner chosen first ≠ outer.cellVertex inner chosen last :=
      fun equal => distinct ((outer.cellVertex_injective inner chosen) equal)
    have childPositive := pairResistance_pos (network inner (configuration chosen))
      (fun child => resistance ⟨chosen, child⟩) (fun child => positive ⟨chosen, child⟩) distinct childReach
    have parentPositive := pairResistance_pos (substitutedNetwork outer inner configuration) resistance positive
      parentDistinct parentReach
    obtain ⟨potential, atFirst, atLast, _, minimal⟩ := exists_pair_minimizer_in_unitInterval
      (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩)
      (fun child => positive ⟨chosen, child⟩) distinct childReach
    obtain ⟨extension, restriction, extensionBound⟩ := exists_cell_preserving_energy_extension
      outer inner configuration resistance positive chosen potential
    have parentLower := pairResistance_energy_lower_bound (substitutedNetwork outer inner configuration)
      resistance positive parentDistinct parentReach extension
    rw [restriction first, restriction last, atFirst, atLast] at parentLower
    norm_num only [zero_sub, neg_one_sq, one_div] at parentLower
    have terminalPositive := (network inner (configuration chosen)).effectiveResistance_pos_of_connected
      (connected_of_crosses inner (configuration chosen) crossing) (fun child => positive ⟨chosen, child⟩)
    have terminalLower := (network inner (configuration chosen)).boundaryPotential_energy_lower_bound
      (connected_of_crosses inner (configuration chosen) crossing) (fun child => positive ⟨chosen, child⟩) potential
    have terminalBound := (div_le_iff₀ terminalPositive).mp terminalLower
    change (potential inner.source - potential inner.target) ^ 2 ≤
      (network inner (configuration chosen)).potentialEnergy (fun child => resistance ⟨chosen, child⟩) potential *
        (network inner (configuration chosen)).effectiveResistance (fun child => resistance ⟨chosen, child⟩) at terminalBound
    have testNonnegative := cellBoundaryTestEnergy_nonnegative outer inner configuration resistance positive chosen
    have upper : (substitutedNetwork outer inner configuration).potentialEnergy resistance extension ≤
        (1 + cellBoundaryTestEnergy outer inner configuration resistance chosen *
          (network inner (configuration chosen)).effectiveResistance (fun child => resistance ⟨chosen, child⟩)) *
        (pairResistance (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩) first last)⁻¹ := by
      calc
        _ ≤ (network inner (configuration chosen)).potentialEnergy (fun child => resistance ⟨chosen, child⟩) potential +
          ((network inner (configuration chosen)).potentialEnergy (fun child => resistance ⟨chosen, child⟩) potential *
            (network inner (configuration chosen)).effectiveResistance (fun child => resistance ⟨chosen, child⟩)) *
              cellBoundaryTestEnergy outer inner configuration resistance chosen :=
          extensionBound.trans (by linarith [mul_le_mul_of_nonneg_right terminalBound testNonnegative])
        _ = _ := by rw [minimal]; ring
    have fraction :
        1 / pairResistance (substitutedNetwork outer inner configuration) resistance
          (outer.cellVertex inner chosen first) (outer.cellVertex inner chosen last) ≤
        (1 + cellBoundaryTestEnergy outer inner configuration resistance chosen *
          (network inner (configuration chosen)).effectiveResistance (fun child => resistance ⟨chosen, child⟩)) /
        pairResistance (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩) first last := by
      simpa only [one_div, div_eq_mul_inv, one_mul] using parentLower.trans upper
    simpa only [one_mul] using (div_le_div_iff₀ parentPositive childPositive).mp fraction
  · obtain rfl := not_ne_iff.mp distinct
    rw [pairResistance_self, pairResistance_self, mul_zero]

end
end IGSIII34.ResistanceLimit
