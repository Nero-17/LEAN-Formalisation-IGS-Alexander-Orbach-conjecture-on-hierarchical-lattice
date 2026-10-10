import IGSIII4.TerminalCore
import IGSIII.Chemical.SubstitutionPaths.MinimalPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem terminalCoreEdges_member_iff_minimal {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (edge : Fin edges) :
    edge ∈ terminalCoreEdges network configuration ↔
      ∃ retained : Configuration edges, MinimalCrossingConfiguration network retained ∧
        (∀ other, retained other = true → configuration other = true) ∧ retained edge = true := by
  classical
  constructor
  · intro membership
    obtain ⟨path, pathMembership, edgeMembership⟩ := Finset.mem_biUnion.mp membership
    exact ⟨configurationOfPath path,
      edgePathFamily_member_minimal network simple configuration crossing pathMembership,
      fun other opened => edgePathFamily_used_edge network simple configuration pathMembership (of_decide_eq_true opened),
      decide_eq_true edgeMembership⟩
  · rintro ⟨retained, minimal, subset, opened⟩
    have pathMembership : openEdges retained ∈ (edgePathFamily network configuration).paths := by
      apply (edgePathFamily_mem_iff_minimal network simple configuration crossing _).mpr
      rw [configurationOfPath_openEdges]
      exact ⟨minimal, fun other member => subset other ((Finset.mem_filter.mp member).2)⟩
    exact Finset.mem_biUnion.mpr ⟨openEdges retained, pathMembership, by simp [openEdges, opened]⟩

end
end IGSIII4
