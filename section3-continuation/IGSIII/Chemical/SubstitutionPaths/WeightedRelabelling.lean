import IGSIII.Chemical.SubstitutionPaths.MinimalPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem networkEquivalence_openEdges_pathCost
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second) (configuration : Configuration firstEdges)
    (cost : Fin secondEdges → ℝ) :
    PathFamily.pathCost (openEdges (equivalence.configuration configuration)) cost =
      PathFamily.pathCost (openEdges configuration) (fun edge => cost (equivalence.edge edge)) := by
  classical
  simp only [PathFamily.pathCost, openEdges, Finset.sum_filter]
  rw [← equivalence.edge.sum_comp]
  simp only [NetworkEquivalence.configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

theorem networkEquivalence_shortest_le
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (firstSimple : Function.Injective (fun edge => s((first.endpoint edge).1, (first.endpoint edge).2)))
    (secondSimple : Function.Injective (fun edge => s((second.endpoint edge).1, (second.endpoint edge).2)))
    (configuration : Configuration firstEdges) (crossing : first.crosses configuration = true)
    (cost : Fin secondEdges → ℝ) :
    (edgePathFamily second (equivalence.configuration configuration)).shortest cost ≤
      (edgePathFamily first configuration).shortest (fun edge => cost (equivalence.edge edge)) := by
  classical
  apply PathFamily.le_shortest
  intro path membership
  have minimal := edgePathFamily_member_minimal first firstSimple configuration crossing membership
  have transportedMinimal := networkEquivalence_minimal equivalence (configurationOfPath path) minimal
  have transportedMembership : openEdges (equivalence.configuration (configurationOfPath path)) ∈
      (edgePathFamily second (equivalence.configuration configuration)).paths := by
    apply (edgePathFamily_mem_iff_minimal second secondSimple _ (by rwa [equivalence.crosses]) _).mpr
    rw [configurationOfPath_openEdges]
    refine ⟨transportedMinimal, ?_⟩
    intro edge member
    have retained := (Finset.mem_filter.mp member).2
    change configurationOfPath path (equivalence.edge.symm edge) = true at retained
    change configuration (equivalence.edge.symm edge) = true
    exact edgePathFamily_used_edge first firstSimple configuration membership (of_decide_eq_true retained)
  calc
    _ ≤ PathFamily.pathCost (openEdges (equivalence.configuration (configurationOfPath path))) cost :=
      PathFamily.shortest_le_pathCost _ _ transportedMembership
    _ = _ := by rw [networkEquivalence_openEdges_pathCost, openEdges_configurationOfPath]

theorem networkEquivalence_edgePathFamily_shortest
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : FiniteNetwork firstVertices firstEdges} {second : FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (firstSimple : Function.Injective (fun edge => s((first.endpoint edge).1, (first.endpoint edge).2)))
    (secondSimple : Function.Injective (fun edge => s((second.endpoint edge).1, (second.endpoint edge).2)))
    (configuration : Configuration firstEdges) (crossing : first.crosses configuration = true)
    (cost : Fin firstEdges → ℝ) :
    (edgePathFamily second (equivalence.configuration configuration)).shortest
        (fun edge => cost (equivalence.edge.symm edge)) =
      (edgePathFamily first configuration).shortest cost := by
  apply le_antisymm
  · have bound := networkEquivalence_shortest_le equivalence firstSimple secondSimple configuration crossing
      (fun edge => cost (equivalence.edge.symm edge))
    simpa only [Equiv.symm_apply_apply] using bound
  · have bound := networkEquivalence_shortest_le equivalence.symm secondSimple firstSimple
      (equivalence.configuration configuration) (by rwa [equivalence.crosses]) cost
    simpa only [NetworkEquivalence.symm, NetworkEquivalence.configuration, Equiv.coe_fn_mk,
      Equiv.symm_symm, Equiv.symm_apply_apply] using bound

end IGSIII.Chemical.Substitution
