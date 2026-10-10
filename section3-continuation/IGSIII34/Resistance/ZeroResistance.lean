import IGSIII34.Resistance.SmallEdges

set_option autoImplicit false
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem zeroEdgeGraph_connected_of_zero_resistance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (resistanceZero : network.effectiveResistance resistance = 0) :
    (network.smallEdgeGraph resistance 0).Reachable network.source network.target := by
  classical
  by_contra disconnected
  let potential : Vertex → ℝ := fun vertex =>
    if (network.smallEdgeGraph resistance 0).Reachable network.source vertex then 1 else 0
  have atSource : potential network.source = 1 := by simp [potential]
  have atTarget : potential network.target = 0 := by simp [potential, disconnected]
  have zeroDifference (edge : Edge) (zero : resistance edge = 0) :
      potential (network.endpoint edge).1 = potential (network.endpoint edge).2 := by
    by_cases same : (network.endpoint edge).1 = (network.endpoint edge).2
    · rw [same]
    · have adjacent : (network.smallEdgeGraph resistance 0).Adj
          (network.endpoint edge).1 (network.endpoint edge).2 := ⟨same, edge, zero.le, Or.inl rfl⟩
      have equivalent : (network.smallEdgeGraph resistance 0).Reachable network.source (network.endpoint edge).1 ↔
          (network.smallEdgeGraph resistance 0).Reachable network.source (network.endpoint edge).2 :=
        ⟨fun reachable => reachable.trans adjacent.reachable,
          fun reachable => reachable.trans adjacent.symm.reachable⟩
      simp only [potential, equivalent]
  obtain ⟨current, unitFlow, _, minimizing⟩ :=
    network.exists_bounded_minimizing_unitFlow_of_nonnegative connected nonnegative
  have cauchy := network.weighted_cauchy_schwarz_of_nonnegative nonnegative current potential zeroDifference
  rw [network.unitFlow_integrationByParts unitFlow, atSource, atTarget, minimizing, resistanceZero] at cauchy
  norm_num at cauchy

end
end IGSIII34.Resistance.FiniteNetwork
