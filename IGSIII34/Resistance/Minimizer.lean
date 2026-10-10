import IGSIII34.Resistance.FlowPaths
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max

/-!
# Existence of a minimizing electrical unit current

Positive edge resistances make every finite-energy sublevel of the Kirchhoff
flow space compact. The minimizer below is obtained from this sublevel, rather
than included as an input certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork

noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem continuous_energy (resistance : Edge → ℝ) : Continuous (energy resistance) := by
  unfold energy
  exact continuous_finsetSum _ (fun edge _ =>
    continuous_const.mul ((continuous_apply edge).pow 2))

theorem continuous_divergence (network : FiniteNetwork Vertex Edge) (vertex : Vertex) :
    Continuous (fun current => network.divergence current vertex) := by
  unfold divergence
  exact continuous_finsetSum _ (fun edge _ => (continuous_apply edge).mul continuous_const)

theorem isClosed_unitFlows (network : FiniteNetwork Vertex Edge) :
    IsClosed network.unitFlows := by
  simpa only [unitFlows, Set.setOf_forall] using
    isClosed_iInter (fun vertex => isClosed_eq (network.continuous_divergence vertex)
      (continuous_const (y := (if vertex = network.source then (1 : ℝ) else 0) -
        (if vertex = network.target then 1 else 0))))

theorem current_sq_le_energy_div {resistance current : Edge → ℝ}
    {floor : ℝ} (floorPositive : 0 < floor)
    (lowerBound : ∀ edge, floor ≤ resistance edge) (edge : Edge) :
    current edge ^ 2 ≤ energy resistance current / floor := by
  rw [le_div_iff₀ floorPositive]
  calc
    current edge ^ 2 * floor ≤ resistance edge * current edge ^ 2 := by
      nlinarith [sq_nonneg (current edge), lowerBound edge]
    _ ≤ energy resistance current :=
      Finset.single_le_sum (fun index _ =>
        mul_nonneg (floorPositive.le.trans (lowerBound index)) (sq_nonneg _)) (Finset.mem_univ edge)

theorem isCompact_flow_sublevel (network : FiniteNetwork Vertex Edge)
    {resistance : Edge → ℝ} {floor bound : ℝ}
    (floorPositive : 0 < floor) (lowerBound : ∀ edge, floor ≤ resistance edge) :
    IsCompact {current | current ∈ network.unitFlows ∧ energy resistance current ≤ bound} := by
  have compactBox : IsCompact {current : Edge → ℝ | ∀ edge,
      current edge ∈ Set.Icc (-Real.sqrt (bound / floor)) (Real.sqrt (bound / floor))} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply compactBox.of_isClosed_subset
  · exact network.isClosed_unitFlows.inter (isClosed_le (continuous_energy resistance) continuous_const)
  · intro current membership edge
    have squareBound := (current_sq_le_energy_div floorPositive lowerBound edge).trans
      ((div_le_div_iff_of_pos_right floorPositive).mpr membership.2)
    have sqrtBound : |current edge| ≤ Real.sqrt (bound / floor) := by
      have nonnegativeBound : 0 ≤ bound / floor := (sq_nonneg (current edge)).trans squareBound
      have sqrtSquare := Real.sq_sqrt nonnegativeBound
      nlinarith [abs_nonneg (current edge), sq_abs (current edge), Real.sqrt_nonneg (bound / floor)]
    exact abs_le.mp sqrtBound

theorem exists_minimizing_unitFlow (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) {resistance : Edge → ℝ}
    {floor : ℝ} (floorPositive : 0 < floor)
    (lowerBound : ∀ edge, floor ≤ resistance edge) :
    ∃ current ∈ network.unitFlows,
      energy resistance current = network.effectiveResistance resistance := by
  obtain ⟨trialCurrent, trialFlow⟩ := feasible
  obtain ⟨current, membership, minimal⟩ :=
    (network.isCompact_flow_sublevel floorPositive lowerBound
      (bound := energy resistance trialCurrent)).exists_isMinOn
      ⟨trialCurrent, trialFlow, le_rfl⟩ (continuous_energy resistance).continuousOn
  refine ⟨current, membership.1, le_antisymm ?_ ?_⟩
  · apply network.le_effectiveResistance ⟨trialCurrent, trialFlow⟩ resistance
    intro competitor competitorFlow
    by_cases competitorBelow : energy resistance competitor ≤ energy resistance trialCurrent
    · exact minimal ⟨competitorFlow, competitorBelow⟩
    · exact membership.2.trans (le_of_lt (lt_of_not_ge competitorBelow))
  · exact network.effectiveResistance_le_energy
      (fun edge => floorPositive.le.trans (lowerBound edge)) membership.1

theorem edges_nonempty_of_feasible (network : FiniteNetwork Vertex Edge)
    (feasible : network.unitFlows.Nonempty) : Nonempty Edge := by
  have cardinalPositive : 0 < Fintype.card Edge := by
    by_contra notPositive
    have emptyUniv : (Finset.univ : Finset Edge) = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos notPositive)
    obtain ⟨current, unitFlow⟩ := feasible
    have sourceLaw := unitFlow network.source
    simp [divergence, emptyUniv, network.distinct] at sourceLaw
  exact Fintype.card_pos_iff.mp cardinalPositive

theorem exists_minimizing_unitFlow_of_positive_resistances
    (network : FiniteNetwork Vertex Edge) (feasible : network.unitFlows.Nonempty)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    ∃ current ∈ network.unitFlows,
      energy resistance current = network.effectiveResistance resistance := by
  letI : Nonempty Edge := network.edges_nonempty_of_feasible feasible
  obtain ⟨edge, _, minimum⟩ := Finset.exists_min_image Finset.univ resistance Finset.univ_nonempty
  exact network.exists_minimizing_unitFlow feasible (positive edge)
    (fun index => minimum index (Finset.mem_univ index))

theorem exists_minimizing_unitFlow_of_connected
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    ∃ current ∈ network.unitFlows,
      energy resistance current = network.effectiveResistance resistance :=
  network.exists_minimizing_unitFlow_of_positive_resistances
    (network.unitFlows_nonempty_of_connected connected) positive

theorem unitFlow_energy_pos (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows) : 0 < energy resistance current := by
  have nonzeroCurrent : ¬ ∀ edge, current edge = 0 := by
    intro allZero
    have sourceLaw := unitFlow network.source
    simp [divergence, allZero, network.distinct] at sourceLaw
  obtain ⟨edge, nonzero⟩ := not_forall.mp nonzeroCurrent
  exact (mul_pos (positive edge) (sq_pos_of_ne_zero nonzero)).trans_le
    (Finset.single_le_sum (fun index _ =>
      mul_nonneg (positive index).le (sq_nonneg _)) (Finset.mem_univ edge))

theorem effectiveResistance_pos_of_connected (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge) :
    0 < network.effectiveResistance resistance := by
  obtain ⟨current, unitFlow, equality⟩ :=
    network.exists_minimizing_unitFlow_of_connected connected positive
  rw [← equality]
  exact network.unitFlow_energy_pos positive unitFlow

end
end IGSIII34.Resistance.FiniteNetwork
