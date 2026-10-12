import IGSIII34.ResistanceLimit.HarmonicCellFlatnessCompletion

/-! A genuine maximum principle for finite cell Dirichlet minimizers. The
proof uses the strictly dissipated energy of the clipping residual and
connectedness to an available boundary terminal. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

theorem upper_clip_square_gap (first last bound : ℝ) :
    ((first - min first bound) - (last - min last bound)) ^ 2 +
      (min first bound - min last bound) ^ 2 ≤ (first - last) ^ 2 := by
  by_cases firstBelow : first ≤ bound <;> by_cases lastBelow : last ≤ bound
  · simp only [min_eq_left firstBelow, min_eq_left lastBelow, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add]
    exact le_rfl
  · rw [min_eq_left firstBelow, min_eq_right (le_of_not_ge lastBelow)]
    nlinarith
  · rw [min_eq_right (le_of_not_ge firstBelow), min_eq_left lastBelow]
    nlinarith
  · rw [min_eq_right (le_of_not_ge firstBelow), min_eq_right (le_of_not_ge lastBelow)]
    nlinarith

theorem finite_upper_clip_energy_gap
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (potential : Vertex → ℝ) (bound : ℝ) :
    network.potentialEnergy resistance (fun vertex => potential vertex - min (potential vertex) bound) +
      network.potentialEnergy resistance (fun vertex => min (potential vertex) bound) ≤
      network.potentialEnergy resistance potential := by
  unfold Resistance.FiniteNetwork.potentialEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro edge _
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (upper_clip_square_gap (potential (network.endpoint edge).1) (potential (network.endpoint edge).2) bound)
    (positive edge).le

theorem cell_trace_minimizer_upper_bound
    {vertices edges : ℕ} (inner : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges)
    (resistance : {edge : Fin edges // configuration edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (potential : Fin vertices → ℝ)
    (minimizing : (network inner configuration).potentialEnergy resistance potential =
      cellTraceEnergy inner configuration resistance (potential inner.source) (potential inner.target))
    (bound : ℝ) (sourceBelow : potential inner.source ≤ bound) (targetBelow : potential inner.target ≤ bound)
    (vertex : Fin vertices)
    (available : (inner.openGraph configuration).Reachable inner.source vertex ∨
      (inner.openGraph configuration).Reachable inner.target vertex) : potential vertex ≤ bound := by
  have clipLower := cellTraceEnergy_le_potentialEnergy inner configuration resistance positive
    (fun vertex => min (potential vertex) bound)
  rw [min_eq_left sourceBelow, min_eq_left targetBelow, ← minimizing] at clipLower
  have gap := finite_upper_clip_energy_gap (network inner configuration) resistance positive potential bound
  have residualNonnegative := (network inner configuration).potentialEnergy_nonnegative positive
    (fun vertex => potential vertex - min (potential vertex) bound)
  have residualZero : (network inner configuration).potentialEnergy resistance
      (fun vertex => potential vertex - min (potential vertex) bound) = 0 := by linarith
  rcases available with fromSource | fromTarget
  · have equal := finite_potential_constant_of_zero_energy (network inner configuration) resistance positive
      (fun vertex => potential vertex - min (potential vertex) bound) residualZero inner.source vertex
      (by rwa [graph_eq_openGraph])
    rw [min_eq_left sourceBelow, sub_self] at equal
    by_contra notBelow
    rw [min_eq_right (le_of_not_ge notBelow)] at equal
    linarith
  · have equal := finite_potential_constant_of_zero_energy (network inner configuration) resistance positive
      (fun vertex => potential vertex - min (potential vertex) bound) residualZero inner.target vertex
      (by rwa [graph_eq_openGraph])
    rw [min_eq_left targetBelow, sub_self] at equal
    by_contra notBelow
    rw [min_eq_right (le_of_not_ge notBelow)] at equal
    linarith

theorem cell_trace_minimizer_lower_bound
    {vertices edges : ℕ} (inner : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges)
    (resistance : {edge : Fin edges // configuration edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (potential : Fin vertices → ℝ)
    (minimizing : (network inner configuration).potentialEnergy resistance potential =
      cellTraceEnergy inner configuration resistance (potential inner.source) (potential inner.target))
    (bound : ℝ) (sourceAbove : bound ≤ potential inner.source) (targetAbove : bound ≤ potential inner.target)
    (vertex : Fin vertices)
    (available : (inner.openGraph configuration).Reachable inner.source vertex ∨
      (inner.openGraph configuration).Reachable inner.target vertex) : bound ≤ potential vertex := by
  have negativeEnergy : (network inner configuration).potentialEnergy resistance (fun vertex => -potential vertex) =
      (network inner configuration).potentialEnergy resistance potential := by
    unfold Resistance.FiniteNetwork.potentialEnergy
    apply Finset.sum_congr rfl
    intro edge _
    congr 1
    ring
  have negativeTrace : cellTraceEnergy inner configuration resistance (-potential inner.source) (-potential inner.target) =
      cellTraceEnergy inner configuration resistance (potential inner.source) (potential inner.target) := by
    unfold cellTraceEnergy
    split_ifs
    · congr 1
      ring
    · rfl
  have upper := cell_trace_minimizer_upper_bound inner configuration resistance positive (fun vertex => -potential vertex)
    (negativeEnergy.trans (minimizing.trans negativeTrace.symm)) (-bound) (by linarith) (by linarith) vertex available
  linarith

theorem cell_trace_minimizer_range
    {vertices edges : ℕ} (inner : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges)
    (resistance : {edge : Fin edges // configuration edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (potential : Fin vertices → ℝ)
    (minimizing : (network inner configuration).potentialEnergy resistance potential =
      cellTraceEnergy inner configuration resistance (potential inner.source) (potential inner.target))
    (vertex : Fin vertices)
    (available : (inner.openGraph configuration).Reachable inner.source vertex ∨
      (inner.openGraph configuration).Reachable inner.target vertex) :
    min (potential inner.source) (potential inner.target) ≤ potential vertex ∧
      potential vertex ≤ max (potential inner.source) (potential inner.target) :=
  ⟨cell_trace_minimizer_lower_bound inner configuration resistance positive potential minimizing _
      (min_le_left _ _) (min_le_right _ _) vertex available,
    cell_trace_minimizer_upper_bound inner configuration resistance positive potential minimizing _
      (le_max_left _ _) (le_max_right _ _) vertex available⟩

end
end IGSIII34.ResistanceLimit
