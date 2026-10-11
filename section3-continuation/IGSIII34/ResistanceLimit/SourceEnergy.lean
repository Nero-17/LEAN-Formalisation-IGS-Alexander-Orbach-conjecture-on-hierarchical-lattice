import IGSIII34.ResistanceLimit.PairResistance

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

def sourceProjection (network : Resistance.FiniteNetwork Vertex Edge) (potential : Vertex → ℝ) (vertex : Vertex) : ℝ :=
  @ite ℝ (network.graph.Reachable network.source vertex) (Classical.propDecidable _) (potential vertex) 0

def sourceComponentEnergy (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (potential : Vertex → ℝ) : ℝ :=
  finiteEnergy network.endpoint (fun edge =>
    @ite ℝ (network.graph.Reachable network.source (network.endpoint edge).1)
      (Classical.propDecidable _) (resistance edge)⁻¹ 0) potential

theorem endpoint_source_reachable_iff (network : Resistance.FiniteNetwork Vertex Edge) (edge : Edge) :
    network.graph.Reachable network.source (network.endpoint edge).1 ↔
      network.graph.Reachable network.source (network.endpoint edge).2 := by
  by_cases equal : (network.endpoint edge).1 = (network.endpoint edge).2
  · rw [equal]
  · have adjacent : network.graph.Adj (network.endpoint edge).1 (network.endpoint edge).2 :=
      ⟨equal, edge, Or.inl (Prod.eta (network.endpoint edge)).symm⟩
    exact ⟨fun reachable => reachable.trans adjacent.reachable,
      fun reachable => reachable.trans adjacent.reachable.symm⟩

theorem sourceComponentEnergy_eq_projectedEnergy (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (potential : Vertex → ℝ) :
    sourceComponentEnergy network resistance potential =
      network.potentialEnergy resistance (sourceProjection network potential) := by
  unfold sourceComponentEnergy finiteEnergy Resistance.FiniteNetwork.potentialEnergy
  apply Finset.sum_congr rfl
  intro edge _
  by_cases firstRetained : network.graph.Reachable network.source (network.endpoint edge).1
  · have lastRetained := (endpoint_source_reachable_iff network edge).mp firstRetained
    simp only [if_pos firstRetained, sourceProjection, if_pos lastRetained, div_eq_mul_inv, mul_comm]
  · have lastAbsent := mt (endpoint_source_reachable_iff network edge).mpr firstRetained
    simp only [if_neg firstRetained, sourceProjection, if_neg lastAbsent, zero_mul, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]

theorem sourceComponentEnergy_nonnegative (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (potential : Vertex → ℝ) :
    0 ≤ sourceComponentEnergy network resistance potential := by
  rw [sourceComponentEnergy_eq_projectedEnergy]
  exact network.potentialEnergy_nonnegative positive _

theorem sourceComponentEnergy_le_potentialEnergy (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (potential : Vertex → ℝ) :
    sourceComponentEnergy network resistance potential ≤ network.potentialEnergy resistance potential := by
  unfold sourceComponentEnergy finiteEnergy Resistance.FiniteNetwork.potentialEnergy
  apply Finset.sum_le_sum
  intro edge _
  by_cases retained : network.graph.Reachable network.source (network.endpoint edge).1
  · simp only [if_pos retained, div_eq_mul_inv, mul_comm, le_refl]
  · simp only [if_neg retained, zero_mul]
    exact div_nonneg (sq_nonneg _) (positive edge).le

/-- Every source-component oscillation is controlled by the genuine finite
effective resistance and the energy of that component alone. -/
theorem sourceComponentEnergy_resistance_bound (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (potential : Vertex → ℝ) {first last : Vertex}
    (firstRetained : network.graph.Reachable network.source first)
    (lastRetained : network.graph.Reachable network.source last) :
    (potential first - potential last) ^ 2 ≤
      pairResistance network resistance first last * sourceComponentEnergy network resistance potential := by
  by_cases distinct : first ≠ last
  · have reachable := firstRetained.symm.trans lastRetained
    have lower := pairResistance_energy_lower_bound network resistance positive distinct reachable (sourceProjection network potential)
    simp only [sourceProjection, if_pos firstRetained, if_pos lastRetained,
      ← sourceComponentEnergy_eq_projectedEnergy] at lower
    have bound := (div_le_iff₀ (pairResistance_pos network resistance positive distinct reachable)).mp lower
    simpa only [mul_comm] using bound
  · obtain rfl := not_ne_iff.mp distinct
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), pairResistance_self, zero_mul, le_refl]

theorem sourceComponentEnergy_eq_zero_iff_constant (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Edge → ℝ) (positive : ∀ edge, 0 < resistance edge) (potential : Vertex → ℝ) :
    sourceComponentEnergy network resistance potential = 0 ↔
      ∀ vertex, network.graph.Reachable network.source vertex → potential vertex = potential network.source := by
  constructor
  · intro energyZero vertex retained
    have bound := sourceComponentEnergy_resistance_bound network resistance positive potential retained
      (SimpleGraph.Reachable.refl network.source)
    rw [energyZero, mul_zero] at bound
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm bound (sq_nonneg _)))
  · intro constant
    rw [sourceComponentEnergy_eq_projectedEnergy]
    unfold Resistance.FiniteNetwork.potentialEnergy
    apply Finset.sum_eq_zero
    intro edge _
    by_cases firstRetained : network.graph.Reachable network.source (network.endpoint edge).1
    · have lastRetained := (endpoint_source_reachable_iff network edge).mp firstRetained
      simp only [sourceProjection, if_pos firstRetained, if_pos lastRetained,
        constant _ firstRetained, constant _ lastRetained, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    · have lastAbsent := mt (endpoint_source_reachable_iff network edge).mpr firstRetained
      simp only [sourceProjection, if_neg firstRetained, if_neg lastAbsent, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]

end
end IGSIII34.ResistanceLimit
