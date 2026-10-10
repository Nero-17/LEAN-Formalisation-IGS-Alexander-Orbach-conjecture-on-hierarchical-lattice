import IGSIII34.Resistance.WeightedPathTrial
import IGSIII34.Resistance.OneEdge
import DeletedNetworkDraft

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open IGSIII.Chemical.Substitution
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem path_current_not_minimizing_without_pivotal_edges (network : FiniteNetwork Vertex Edge)
    (noPivotal : ∀ removed, (network.graphWithoutEdge removed).Reachable network.source network.target)
    {resistance current : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (squares : ∀ edge, current edge ^ 2 = 0 ∨ current edge ^ 2 = 1) :
    energy resistance current ≠ network.effectiveResistance resistance := by
  intro minimal
  have existsNonzero : ∃ edge, current edge ≠ 0 := by
    by_contra none
    have zeroAll : ∀ edge, current edge = 0 := by
      intro edge
      by_contra nonzero
      exact none ⟨edge, nonzero⟩
    have divergenceZero : network.divergence current network.source = 0 := by simp [divergence, zeroAll]
    have divergenceOne : network.divergence current network.source = 1 := by
      simpa only [ite_true, if_neg network.distinct, sub_zero] using unitFlow network.source
    linarith
  obtain ⟨removed, nonzero⟩ := existsNonzero
  have removedSquare : current removed ^ 2 = 1 :=
    (squares removed).resolve_left (fun zeroSquare => nonzero (sq_eq_zero_iff.mp zeroSquare))
  obtain ⟨competitor, competitorFlow, avoidsEdge, competitorBound⟩ :=
    network.exists_bounded_unitFlow_avoiding_edge removed (noPivotal removed)
  have termNonpositive (edge : Edge) :
      resistance edge * current edge * (competitor edge - current edge) ≤ 0 := by
    rcases squares edge with zeroSquare | unitSquare
    · have zeroCurrent := sq_eq_zero_iff.mp zeroSquare
      simp only [zeroCurrent, mul_zero, zero_mul, le_refl]
    · have absCurrent : |current edge| = 1 := by nlinarith [abs_nonneg (current edge), sq_abs (current edge)]
      have productBound : current edge * competitor edge ≤ 1 := by
        calc
          _ ≤ |current edge * competitor edge| := le_abs_self _
          _ = |current edge| * |competitor edge| := abs_mul _ _
          _ ≤ 1 := by simpa only [absCurrent, one_mul] using competitorBound edge
      calc
        _ = resistance edge * (current edge * competitor edge - current edge ^ 2) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (positive edge).le (by rw [unitSquare]; linarith)
  have removedStrict : resistance removed * current removed * (competitor removed - current removed) < 0 := by
    rw [avoidsEdge, zero_sub]
    nlinarith [positive removed]
  have crossNegative : crossEnergy resistance current (fun edge => competitor edge - current edge) < 0 := by
    have bound := Finset.sum_lt_sum (fun edge (_ : edge ∈ (Finset.univ : Finset Edge)) => termNonpositive edge)
      ⟨removed, Finset.mem_univ _, removedStrict⟩
    simpa only [crossEnergy, Finset.sum_const_zero] using bound
  have crossZero := network.minimizing_current_orthogonal positive unitFlow minimal
    (network.unitFlow_sub_zero_divergence competitorFlow unitFlow)
  linarith

theorem effectiveResistance_lt_weightedDistance (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (noPivotal : ∀ removed, (network.graphWithoutEdge removed).Reachable network.source network.target)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (cost : Sym2 Vertex → ℝ)
    (consistent : ∀ edge, resistance edge = cost s((network.endpoint edge).1, (network.endpoint edge).2)) :
    network.effectiveResistance resistance <
      weightedDistance network.graph cost network.source network.target := by
  obtain ⟨walk, simple, minimizing⟩ := exists_weighted_geodesic network.graph cost connected
  obtain ⟨current, unitFlow, squares, _, energyIdentity⟩ :=
    network.exists_weighted_path_flow resistance cost consistent walk simple
  have bound := network.effectiveResistance_le_energy (fun edge => (positive edge).le) unitFlow
  have notMinimal := network.path_current_not_minimizing_without_pivotal_edges noPivotal positive unitFlow squares
  exact (lt_of_le_of_ne bound (Ne.symm notMinimal)).trans_eq (energyIdentity.trans minimizing)

end
end IGSIII34.Resistance.FiniteNetwork
