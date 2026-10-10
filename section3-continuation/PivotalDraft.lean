import IGSIII34.Resistance.CurrentBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def graphWithoutEdge (network : FiniteNetwork Vertex Edge) (removed : Edge) : SimpleGraph Vertex where
  Adj first second := first ≠ second ∧ ∃ edge, edge ≠ removed ∧
    (network.endpoint edge = (first, second) ∨ network.endpoint edge = (second, first))
  symm := ⟨by
    rintro first second ⟨distinct, edge, retained, orientation⟩
    exact ⟨distinct.symm, edge, retained, orientation.symm⟩⟩
  loopless := ⟨by intro vertex adjacency; exact adjacency.1 rfl⟩

def deletionCut (network : FiniteNetwork Vertex Edge) (removed : Edge) (vertex : Vertex) : ℝ := by
  classical
  exact if (network.graphWithoutEdge removed).Reachable network.source vertex then 1 else 0

theorem deletionCut_equal_on_retained_edge (network : FiniteNetwork Vertex Edge)
    (removed : Edge) {edge : Edge} (retained : edge ≠ removed) :
    network.deletionCut removed (network.endpoint edge).1 =
      network.deletionCut removed (network.endpoint edge).2 := by
  classical
  by_cases same : (network.endpoint edge).1 = (network.endpoint edge).2
  · rw [same]
  · have adjacent : (network.graphWithoutEdge removed).Adj
        (network.endpoint edge).1 (network.endpoint edge).2 :=
      ⟨same, edge, retained, Or.inl rfl⟩
    have reachableEquivalent :
        (network.graphWithoutEdge removed).Reachable network.source (network.endpoint edge).1 ↔
          (network.graphWithoutEdge removed).Reachable network.source (network.endpoint edge).2 :=
      ⟨fun reachable => reachable.trans adjacent.reachable,
        fun reachable => reachable.trans adjacent.symm.reachable⟩
    simp only [deletionCut, reachableEquivalent]

theorem pivotal_edge_current_sq_eq_one (network : FiniteNetwork Vertex Edge)
    {current : Edge → ℝ} (unitFlow : current ∈ network.unitFlows) (removed : Edge)
    (pivotal : ¬ (network.graphWithoutEdge removed).Reachable network.source network.target) :
    current removed ^ 2 = 1 := by
  classical
  have cutIdentity := network.unitFlow_integrationByParts unitFlow (network.deletionCut removed)
  have sourceValue : network.deletionCut removed network.source = 1 := by simp [deletionCut]
  have targetValue : network.deletionCut removed network.target = 0 := by simp [deletionCut, pivotal]
  rw [sourceValue, targetValue, sub_zero] at cutIdentity
  have allOthersZero (edge : Edge) (_ : edge ∈ (Finset.univ : Finset Edge)) (different : edge ≠ removed) :
      current edge * (network.deletionCut removed (network.endpoint edge).1 -
        network.deletionCut removed (network.endpoint edge).2) = 0 := by
    rw [network.deletionCut_equal_on_retained_edge removed different, sub_self, mul_zero]
  rw [Finset.sum_eq_single removed allOthersZero (by simp)] at cutIdentity
  unfold deletionCut at cutIdentity
  split_ifs at cutIdentity <;> norm_num at cutIdentity
  all_goals nlinarith

theorem sum_pivotal_resistances_le_energy (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (unitFlow : current ∈ network.unitFlows) (pivotalEdges : Finset Edge)
    (pivotal : ∀ edge ∈ pivotalEdges,
      ¬ (network.graphWithoutEdge edge).Reachable network.source network.target) :
    ∑ edge ∈ pivotalEdges, resistance edge ≤ energy resistance current := by
  calc
    _ = ∑ edge ∈ pivotalEdges, resistance edge * current edge ^ 2 := by
      apply Finset.sum_congr rfl
      intro edge membership
      rw [network.pivotal_edge_current_sq_eq_one unitFlow edge (pivotal edge membership), mul_one]
    _ ≤ energy resistance current := Finset.sum_le_univ_sum_of_nonneg
      (fun edge => mul_nonneg (nonnegative edge) (sq_nonneg _))

theorem sum_pivotal_resistances_le_effectiveResistance (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {resistance : Edge → ℝ}
    (nonnegative : ∀ edge, 0 ≤ resistance edge) (pivotalEdges : Finset Edge)
    (pivotal : ∀ edge ∈ pivotalEdges,
      ¬ (network.graphWithoutEdge edge).Reachable network.source network.target) :
    ∑ edge ∈ pivotalEdges, resistance edge ≤ network.effectiveResistance resistance := by
  apply network.le_effectiveResistance feasible
  intro current unitFlow
  exact network.sum_pivotal_resistances_le_energy nonnegative unitFlow pivotalEdges pivotal

end
end IGSIII34.Resistance.FiniteNetwork
