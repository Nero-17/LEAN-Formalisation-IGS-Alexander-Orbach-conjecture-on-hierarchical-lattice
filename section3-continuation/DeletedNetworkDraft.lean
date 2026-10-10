import IGSIII34.Resistance.Pivotal
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def deletedNetwork (network : FiniteNetwork Vertex Edge) (removed : Edge) :
    FiniteNetwork Vertex {edge : Edge // edge ≠ removed} where
  endpoint edge := network.endpoint edge.val
  source := network.source
  target := network.target
  distinct := network.distinct

theorem deletedNetwork_graph (network : FiniteNetwork Vertex Edge) (removed : Edge) :
    (network.deletedNetwork removed).graph = network.graphWithoutEdge removed := by
  ext first second
  constructor
  · rintro ⟨distinct, ⟨edge, retained⟩, orientation⟩
    exact ⟨distinct, edge, retained, orientation⟩
  · rintro ⟨distinct, edge, retained, orientation⟩
    exact ⟨distinct, ⟨edge, retained⟩, orientation⟩

def extendDeletedCurrent (removed : Edge) (current : {edge : Edge // edge ≠ removed} → ℝ) : Edge → ℝ :=
  fun edge => if retained : edge ≠ removed then current ⟨edge, retained⟩ else 0

theorem extendDeletedCurrent_divergence (network : FiniteNetwork Vertex Edge)
    (removed : Edge) (current : {edge : Edge // edge ≠ removed} → ℝ) (vertex : Vertex) :
    network.divergence (extendDeletedCurrent removed current) vertex =
      (network.deletedNetwork removed).divergence current vertex := by
  classical
  unfold divergence extendDeletedCurrent deletedNetwork
  simp only [dite_mul, zero_mul]
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  exact (Equiv.subtypeEquivRight (by simp)).sum_comp
    (fun edge : {edge : Edge // edge ≠ removed} => current edge *
      ((if (network.endpoint edge.val).1 = vertex then 1 else 0) -
        (if (network.endpoint edge.val).2 = vertex then 1 else 0)))

theorem extendDeletedCurrent_unitFlow (network : FiniteNetwork Vertex Edge)
    (removed : Edge) (current : {edge : Edge // edge ≠ removed} → ℝ)
    (unitFlow : current ∈ (network.deletedNetwork removed).unitFlows) :
    extendDeletedCurrent removed current ∈ network.unitFlows := by
  intro vertex
  rw [network.extendDeletedCurrent_divergence]
  exact unitFlow vertex

theorem exists_bounded_unitFlow_avoiding_edge (network : FiniteNetwork Vertex Edge)
    (removed : Edge)
    (connectedAfterDeletion : (network.graphWithoutEdge removed).Reachable network.source network.target) :
    ∃ current ∈ network.unitFlows, current removed = 0 ∧ ∀ edge, |current edge| ≤ 1 := by
  have connected : (network.deletedNetwork removed).graph.Reachable
      (network.deletedNetwork removed).source (network.deletedNetwork removed).target := by
    change (network.deletedNetwork removed).graph.Reachable network.source network.target
    rwa [deletedNetwork_graph]
  obtain ⟨current, unitFlow, minimal⟩ := (network.deletedNetwork removed).exists_minimizing_unitFlow_of_connected
    connected (fun _ => zero_lt_one)
  have currentBound := (network.deletedNetwork removed).minimizing_current_abs_le_one
    (fun _ => zero_lt_one) unitFlow minimal
  refine ⟨extendDeletedCurrent removed current, network.extendDeletedCurrent_unitFlow removed current unitFlow,
    by simp [extendDeletedCurrent], ?_⟩
  intro edge
  by_cases retained : edge ≠ removed
  · simpa only [extendDeletedCurrent, dif_pos retained] using currentBound ⟨edge, retained⟩
  · simp [extendDeletedCurrent, retained]

end
end IGSIII34.Resistance.FiniteNetwork
