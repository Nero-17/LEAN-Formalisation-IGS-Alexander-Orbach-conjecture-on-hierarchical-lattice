import IGSIII34.ResistanceLimit.SourceEnergy

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem exists_source_pair_minimizer (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    {first last : Vertex} (distinct : first ≠ last)
    (firstRetained : network.graph.Reachable network.source first)
    (lastRetained : network.graph.Reachable network.source last) :
    ∃ potential : Vertex → ℝ, potential first = 0 ∧ potential last = 1 ∧
      sourceComponentEnergy network resistance potential = (pairResistance network resistance first last)⁻¹ := by
  have reachable := firstRetained.symm.trans lastRetained
  obtain ⟨potential, atFirst, atLast, minimizing⟩ :=
    (retarget network first last distinct).exists_boundaryPotential_minimizer reachable positive 0 1
  change potential first = 0 at atFirst
  change potential last = 1 at atLast
  have energyIdentity : network.potentialEnergy resistance potential =
      (pairResistance network resistance first last)⁻¹ := by
    simpa only [Resistance.FiniteNetwork.potentialEnergy, retarget, pairResistance, dif_pos distinct,
      zero_sub, neg_one_sq, one_div] using minimizing
  refine ⟨potential, atFirst, atLast, le_antisymm ?_ ?_⟩
  · exact (sourceComponentEnergy_le_potentialEnergy network resistance positive potential).trans energyIdentity.le
  · have bound := sourceComponentEnergy_resistance_bound network resistance positive potential firstRetained lastRetained
    rw [atFirst, atLast] at bound
    norm_num only [zero_sub, neg_one_sq] at bound
    have lower := (div_le_iff₀ (pairResistance_pos network resistance positive distinct reachable)).mpr
      (show 1 ≤ sourceComponentEnergy network resistance potential * pairResistance network resistance first last by
        simpa only [mul_comm] using bound)
    simpa only [one_div] using lower

end
end IGSIII34.ResistanceLimit
