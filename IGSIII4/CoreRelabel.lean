import IGSIII4.CoreMinimalCharacterization
import IGSIII.Chemical.SubstitutionPaths.MinimalGeneration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem terminalCoreEdges_networkEquivalence_forward
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (firstSimple : Function.Injective (fun edge => s((first.endpoint edge).1, (first.endpoint edge).2)))
    (secondSimple : Function.Injective (fun edge => s((second.endpoint edge).1, (second.endpoint edge).2)))
    (configuration : Configuration firstEdges) (crossing : first.crosses configuration = true)
    (edge : Fin firstEdges) (membership : edge ∈ terminalCoreEdges first configuration) :
    equivalence.edge edge ∈ terminalCoreEdges second (equivalence.configuration configuration) := by
  obtain ⟨retained, minimal, subset, opened⟩ :=
    (terminalCoreEdges_member_iff_minimal first firstSimple configuration crossing edge).mp membership
  apply (terminalCoreEdges_member_iff_minimal second secondSimple _
    ((equivalence.crosses configuration).trans crossing) _).mpr
  refine ⟨equivalence.configuration retained, networkEquivalence_minimal equivalence retained minimal, ?_, ?_⟩
  · intro other retainedHere
    exact subset (equivalence.edge.symm other) retainedHere
  · simpa only [NetworkEquivalence.configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using opened

theorem terminalCoreEdges_networkEquivalence_member
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (firstSimple : Function.Injective (fun edge => s((first.endpoint edge).1, (first.endpoint edge).2)))
    (secondSimple : Function.Injective (fun edge => s((second.endpoint edge).1, (second.endpoint edge).2)))
    (configuration : Configuration firstEdges) (crossing : first.crosses configuration = true)
    (edge : Fin firstEdges) :
    equivalence.edge edge ∈ terminalCoreEdges second (equivalence.configuration configuration) ↔
      edge ∈ terminalCoreEdges first configuration := by
  refine ⟨fun membership => ?_, terminalCoreEdges_networkEquivalence_forward
    equivalence firstSimple secondSimple configuration crossing edge⟩
  have inverseConfiguration : equivalence.symm.configuration (equivalence.configuration configuration) = configuration := by
    funext other
    simp [NetworkEquivalence.symm, NetworkEquivalence.configuration]
  have backward := terminalCoreEdges_networkEquivalence_forward equivalence.symm secondSimple firstSimple
    (equivalence.configuration configuration) ((equivalence.crosses configuration).trans crossing)
    (equivalence.edge edge) membership
  change equivalence.edge.symm (equivalence.edge edge) ∈ terminalCoreEdges first
    (equivalence.symm.configuration (equivalence.configuration configuration)) at backward
  rwa [inverseConfiguration, Equiv.symm_apply_apply] at backward

end
end IGSIII4
