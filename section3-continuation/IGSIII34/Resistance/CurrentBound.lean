import IGSIII34.Resistance.IntegrationByParts

/-!
# Every optimal unit-current edge has magnitude at most one

The proof uses the cut above an endpoint's potential. All currents crossing
this cut have the same sign, while its total current is at most one by
Kirchhoff's law. No acyclic-flow decomposition is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def levelCut (potential : Vertex → ℝ) (threshold : ℝ) (vertex : Vertex) : ℝ :=
  if threshold ≤ potential vertex then 1 else 0

theorem levelCut_current_nonnegative (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} {potential : Vertex → ℝ}
    (positive : ∀ edge, 0 < resistance edge)
    (ohm : ∀ edge, resistance edge * current edge =
      potential (network.endpoint edge).1 - potential (network.endpoint edge).2)
    (threshold : ℝ) (edge : Edge) :
    0 ≤ current edge *
      (levelCut potential threshold (network.endpoint edge).1 -
        levelCut potential threshold (network.endpoint edge).2) := by
  unfold levelCut
  split_ifs with firstAbove secondAbove secondAbove
  · simp
  · simp only [sub_zero, mul_one]
    have positiveProduct : 0 < resistance edge * current edge := by
      rw [ohm]
      linarith
    exact ((mul_pos_iff_of_pos_left (positive edge)).mp positiveProduct).le
  · simp only [zero_sub, mul_neg, mul_one]
    have negativeProduct : resistance edge * current edge < 0 := by
      rw [ohm]
      linarith
    have negativeCurrent : current edge < 0 :=
      (mul_lt_mul_iff_of_pos_left (positive edge)).mp (by simpa using negativeProduct)
    linarith
  · simp

theorem levelCut_total_current_le_one (network : FiniteNetwork Vertex Edge)
    {current : Edge → ℝ} (unitFlow : current ∈ network.unitFlows)
    (potential : Vertex → ℝ) (threshold : ℝ) :
    ∑ edge, current edge *
      (levelCut potential threshold (network.endpoint edge).1 -
        levelCut potential threshold (network.endpoint edge).2) ≤ 1 := by
  rw [network.unitFlow_integrationByParts unitFlow]
  unfold levelCut
  split_ifs <;> norm_num

theorem ohmic_unitFlow_current_abs_le_one (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} {potential : Vertex → ℝ}
    (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (ohm : ∀ edge, resistance edge * current edge =
      potential (network.endpoint edge).1 - potential (network.endpoint edge).2)
    (edge : Edge) : |current edge| ≤ 1 := by
  by_cases currentNonnegative : 0 ≤ current edge
  · rw [abs_of_nonneg currentNonnegative]
    by_cases currentZero : current edge = 0
    · simp [currentZero]
    · have currentPositive : 0 < current edge :=
        lt_of_le_of_ne currentNonnegative (Ne.symm currentZero)
      have firstHigher : potential (network.endpoint edge).2 < potential (network.endpoint edge).1 := by
        have productPositive := mul_pos (positive edge) currentPositive
        rw [ohm] at productPositive
        linarith
      have edgeTerm := Finset.single_le_sum
        (fun index _ => network.levelCut_current_nonnegative positive ohm
          (potential (network.endpoint edge).1) index) (Finset.mem_univ edge)
      have totalBound := network.levelCut_total_current_le_one unitFlow potential
        (potential (network.endpoint edge).1)
      have edgeBound := edgeTerm.trans totalBound
      simpa [levelCut, not_le.mpr firstHigher] using edgeBound
  · have currentNegative : current edge < 0 := lt_of_not_ge currentNonnegative
    rw [abs_of_neg currentNegative]
    have secondHigher : potential (network.endpoint edge).1 < potential (network.endpoint edge).2 := by
      have productNegative := mul_neg_of_pos_of_neg (positive edge) currentNegative
      rw [ohm] at productNegative
      linarith
    have edgeTerm := Finset.single_le_sum
      (fun index _ => network.levelCut_current_nonnegative positive ohm
        (potential (network.endpoint edge).2) index) (Finset.mem_univ edge)
    have totalBound := network.levelCut_total_current_le_one unitFlow potential
      (potential (network.endpoint edge).2)
    have edgeBound := edgeTerm.trans totalBound
    simpa [levelCut, not_le.mpr secondHigher] using edgeBound

theorem minimizing_current_abs_le_one (network : FiniteNetwork Vertex Edge)
    {resistance current : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (minimal : energy resistance current = network.effectiveResistance resistance)
    (edge : Edge) : |current edge| ≤ 1 := by
  obtain ⟨potential, ohm⟩ := network.minimizing_current_has_potential positive unitFlow minimal
  exact network.ohmic_unitFlow_current_abs_le_one positive unitFlow ohm edge

end
end IGSIII34.Resistance.FiniteNetwork
