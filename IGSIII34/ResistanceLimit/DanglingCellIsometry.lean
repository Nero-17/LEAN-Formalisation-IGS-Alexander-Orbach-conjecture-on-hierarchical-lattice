import IGSIII34.ResistanceLimit.CellPreservedEnergy
import IGSIII34.ResistanceLimit.SeparatedTerminalPotential
import IGSIII34.ResistanceLimit.ElectricalRadius

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Either full one-terminal component of a noncrossing cell embeds
isometrically in the actual ambient electrical graph, including dangling
branches at every retained vertex. -/
theorem substituted_dangling_cell_pairResistance_eq
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (chosen : Fin outerEdges)
    (noncrossing : inner.crosses (configuration chosen) = false) (sourceSide : Bool)
    (first last : Fin innerVertices)
    (firstRetained : (network inner (configuration chosen)).graph.Reachable
      (sideNetwork (network inner (configuration chosen)) sourceSide).source first)
    (lastRetained : (network inner (configuration chosen)).graph.Reachable
      (sideNetwork (network inner (configuration chosen)) sourceSide).source last) :
    pairResistance (substitutedNetwork outer inner configuration) resistance
      (outer.cellVertex inner chosen first) (outer.cellVertex inner chosen last) =
    pairResistance (network inner (configuration chosen)) (fun child => resistance ⟨chosen, child⟩) first last := by
  have childReach := firstRetained.symm.trans lastRetained
  have reachable : (inner.openGraph (configuration chosen)).Reachable first last := by
    rwa [graph_eq_openGraph] at childReach
  apply le_antisymm
  · exact substituted_child_pairResistance_le outer inner configuration resistance positive chosen first last reachable
  · by_cases distinct : first ≠ last
    · have disconnected : ¬ (network inner (configuration chosen)).graph.Reachable
          (network inner (configuration chosen)).source (network inner (configuration chosen)).target := by
        intro reach
        have crosses : inner.crosses (configuration chosen) = true :=
          (inner.crosses_eq_true _).mpr (by rwa [← graph_eq_openGraph])
        rw [noncrossing] at crosses
        exact Bool.false_ne_true crosses
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
      obtain ⟨potential, atSource, atTarget, difference, energy⟩ :=
        exists_pair_potential_zero_at_separated_terminals (network inner (configuration chosen))
          (fun child => resistance ⟨chosen, child⟩) (fun child => positive ⟨chosen, child⟩)
          sourceSide disconnected distinct firstRetained lastRetained
      change potential inner.source = 0 at atSource
      change potential inner.target = 0 at atTarget
      obtain ⟨extension, restriction, extensionBound⟩ := exists_cell_preserving_energy_extension
        outer inner configuration resistance positive chosen potential
      rw [atSource, atTarget, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero] at extensionBound
      have lower := pairResistance_energy_lower_bound (substitutedNetwork outer inner configuration)
        resistance positive parentDistinct parentReach extension
      rw [restriction first, restriction last, difference, one_div] at lower
      exact (inv_le_inv₀ parentPositive childPositive).mp (lower.trans (extensionBound.trans energy))
    · obtain rfl := not_ne_iff.mp distinct
      rw [pairResistance_self, pairResistance_self]

end
end IGSIII34.ResistanceLimit
