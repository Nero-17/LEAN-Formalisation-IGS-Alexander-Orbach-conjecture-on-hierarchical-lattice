import IGSIII34.Resistance.Connectivity
import IGSIII34.Resistance.Nonnegative

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem weighted_cauchy_schwarz_of_nonnegative (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge)
    (current : Edge → ℝ) (potential : Vertex → ℝ)
    (zeroDifference : ∀ edge, resistance edge = 0 →
      potential (network.endpoint edge).1 = potential (network.endpoint edge).2) :
    (∑ edge, current edge *
      (potential (network.endpoint edge).1 - potential (network.endpoint edge).2)) ^ 2 ≤
        energy resistance current * network.potentialEnergy resistance potential := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun edge => Real.sqrt (resistance edge) * current edge)
    (fun edge => (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) /
      Real.sqrt (resistance edge))
  have productIdentity (edge : Edge) :
      (Real.sqrt (resistance edge) * current edge) *
          ((potential (network.endpoint edge).1 - potential (network.endpoint edge).2) /
            Real.sqrt (resistance edge)) =
        current edge * (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) := by
    by_cases zero : resistance edge = 0
    · simp [zero, zeroDifference edge zero]
    · field_simp [ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (nonnegative edge) (Ne.symm zero)))]
  have currentSquare (edge : Edge) : (Real.sqrt (resistance edge) * current edge) ^ 2 =
      resistance edge * current edge ^ 2 := by rw [mul_pow, Real.sq_sqrt (nonnegative edge)]
  have potentialSquare (edge : Edge) :
      ((potential (network.endpoint edge).1 - potential (network.endpoint edge).2) /
          Real.sqrt (resistance edge)) ^ 2 =
        (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 /
          resistance edge := by rw [div_pow, Real.sq_sqrt (nonnegative edge)]
  simpa only [productIdentity, currentSquare, potentialSquare, energy, potentialEnergy] using cauchy

def smallEdgeGraph (network : FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (threshold : ℝ) : SimpleGraph Vertex where
  Adj first second := first ≠ second ∧ ∃ edge, resistance edge ≤ threshold ∧
    (network.endpoint edge = (first, second) ∨ network.endpoint edge = (second, first))
  symm := ⟨by
    rintro first second ⟨distinct, edge, small, orientation⟩
    exact ⟨distinct.symm, edge, small, orientation.symm⟩⟩
  loopless := ⟨by intro vertex adjacency; exact adjacency.1 rfl⟩

theorem connected_edge_card_pos (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    0 < Fintype.card Edge := by
  obtain ⟨current, unitFlow⟩ := network.unitFlows_nonempty_of_connected connected
  by_contra noEdges
  have empty : Fintype.card Edge = 0 := Nat.eq_zero_of_not_pos noEdges
  letI : IsEmpty Edge := Fintype.card_eq_zero_iff.mp empty
  have sourceLaw := unitFlow network.source
  simp [divergence, network.distinct] at sourceLaw

theorem smallEdgeGraph_connected_of_resistance_le (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge)
    {bound : ℝ} (boundPositive : 0 < bound)
    (resistanceBound : network.effectiveResistance resistance ≤ bound) :
    (network.smallEdgeGraph resistance ((Fintype.card Edge : ℝ) * bound)).Reachable
      network.source network.target := by
  classical
  by_contra disconnected
  let potential : Vertex → ℝ := fun vertex =>
    if (network.smallEdgeGraph resistance ((Fintype.card Edge : ℝ) * bound)).Reachable
      network.source vertex then 1 else 0
  have atSource : potential network.source = 1 := by simp [potential]
  have atTarget : potential network.target = 0 := by simp [potential, disconnected]
  have cardPositive : 0 < (Fintype.card Edge : ℝ) := by
    exact_mod_cast network.connected_edge_card_pos connected
  have thresholdPositive : 0 < (Fintype.card Edge : ℝ) * bound := mul_pos cardPositive boundPositive
  have smallDifference (edge : Edge)
      (small : resistance edge ≤ (Fintype.card Edge : ℝ) * bound) :
      potential (network.endpoint edge).1 = potential (network.endpoint edge).2 := by
    by_cases same : (network.endpoint edge).1 = (network.endpoint edge).2
    · rw [same]
    · have adjacent : (network.smallEdgeGraph resistance ((Fintype.card Edge : ℝ) * bound)).Adj
          (network.endpoint edge).1 (network.endpoint edge).2 := ⟨same, edge, small, Or.inl rfl⟩
      have equivalent :
          (network.smallEdgeGraph resistance ((Fintype.card Edge : ℝ) * bound)).Reachable
            network.source (network.endpoint edge).1 ↔
          (network.smallEdgeGraph resistance ((Fintype.card Edge : ℝ) * bound)).Reachable
            network.source (network.endpoint edge).2 :=
        ⟨fun reachable => reachable.trans adjacent.reachable,
          fun reachable => reachable.trans adjacent.symm.reachable⟩
      simp only [potential, equivalent]
  have squareBound (edge : Edge) :
      (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 ≤ 1 := by
    unfold potential
    split_ifs <;> norm_num
  have termStrict (edge : Edge) :
      (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 /
          resistance edge < 1 / ((Fintype.card Edge : ℝ) * bound) := by
    by_cases small : resistance edge ≤ (Fintype.card Edge : ℝ) * bound
    · rw [smallDifference edge small]
      simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div] using
        one_div_pos.mpr thresholdPositive
    · have large : (Fintype.card Edge : ℝ) * bound < resistance edge := lt_of_not_ge small
      calc
        _ ≤ 1 / resistance edge := div_le_div_of_nonneg_right (squareBound edge)
          (thresholdPositive.trans large).le
        _ < _ := one_div_lt_one_div_of_lt thresholdPositive large
  have potentialEnergyBound : network.potentialEnergy resistance potential < 1 / bound := by
    unfold potentialEnergy
    calc
      _ < ∑ _edge : Edge, 1 / ((Fintype.card Edge : ℝ) * bound) := by
        exact Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by simpa using network.connected_edge_card_pos connected))
          (fun edge _ => termStrict edge)
      _ = 1 / bound := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [ne_of_gt cardPositive, ne_of_gt boundPositive]
  obtain ⟨current, unitFlow, _, minimizing⟩ :=
    network.exists_bounded_minimizing_unitFlow_of_nonnegative connected nonnegative
  have cauchy := network.weighted_cauchy_schwarz_of_nonnegative nonnegative current potential
    (fun edge zero => smallDifference edge (by rw [zero]; exact thresholdPositive.le))
  rw [network.unitFlow_integrationByParts unitFlow, atSource, atTarget, minimizing] at cauchy
  norm_num only [sub_zero, one_pow] at cauchy
  have energyNonnegative : 0 ≤ network.potentialEnergy resistance potential :=
    Finset.sum_nonneg (fun edge _ => div_nonneg (sq_nonneg _) (nonnegative edge))
  have productStrict : bound * network.potentialEnergy resistance potential < 1 := by
    have multiplied := mul_lt_mul_of_pos_left potentialEnergyBound boundPositive
    simpa [ne_of_gt boundPositive] using multiplied
  nlinarith [mul_le_mul_of_nonneg_right resistanceBound energyNonnegative]

end
end IGSIII34.Resistance.FiniteNetwork
