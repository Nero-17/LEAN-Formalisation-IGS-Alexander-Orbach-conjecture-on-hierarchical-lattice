import Universality.Percolation.MassDistributionSmoothing
import Universality.Probability.IndependentSupport
import Universality.Percolation.AllClosedCharacteristic

namespace Universality.FiniteNetwork
noncomputable section
open MeasureTheory
open scoped ENNReal

theorem offspringMassLaw_support {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (radius : ℝ) (state : LiveState) (coarse : Configuration edges)
    (point : Fin edges → ℝ) (hpoint : ∀ edge, point edge ∈ (R.childMassLaw law state coarse edge).support) :
    (∑ edge, point edge) / radius ∈ (R.offspringMassLaw law radius state coarse).support := by
  have h := continuous_map_support (independentSumLaw (R.childMassLaw law state coarse))
    (fun x => radius⁻¹ * x) (by fun_prop) (∑ edge, point edge)
    (independent_sum_support _ point hpoint)
  simpa only [offspringMassLaw, div_eq_mul_inv, mul_comm] using h

theorem smoothing_branch_support {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (p radius : ℝ) (state : LiveState)
    (hsmoothing : law state = finiteMixtureLaw (R.conditionalCellWeight p (state == .connected))
      (R.offspringMassLaw law radius state))
    (coarse : Configuration edges) (hpositive : 0 < R.conditionalCellWeight p (state == .connected) coarse)
    (point : Fin edges → ℝ) (hpoint : ∀ edge, point edge ∈ (R.childMassLaw law state coarse edge).support) :
    (∑ edge, point edge) / radius ∈ (law state).support := by
  rw [hsmoothing]
  exact finite_mixture_support _ _ coarse hpositive _ (R.offspringMassLaw_support law radius state coarse point hpoint)

theorem offspringMassLaw_allClosed_single {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)] (radius : ℝ) :
    R.offspringMassLaw law radius .single (fun _ => false) =
      (independentSumLaw (fun _ : Fin R.sourceIncidentEdges.card => law .single)).map (fun x => radius⁻¹ * x) := by
  classical
  apply Measure.ext_of_charFun
  funext t
  rw [R.offspringMassLaw_charFun, charFun_map_mul, independentSumLaw_charFun]
  calc
    _ = charFun (law .single) (t / radius) ^ R.sourceIncidentEdges.card := by
      have hfactor (edge : Fin edges) :
          (match R.childState .single (fun _ => false) edge with
            | none => (1 : ℂ)
            | some child => charFun (law child) (t / radius)) =
          if edge ∈ R.sourceIncidentEdges then charFun (law .single) (t / radius) else 1 := by
        by_cases hincident : edge ∈ R.sourceIncidentEdges
        · rw [if_pos hincident, R.childState_allClosed_single edge (Finset.mem_filter.mp hincident).2]
        · rw [if_neg hincident]
          have hne : (R.endpoint edge).1 ≠ R.source ∧ (R.endpoint edge).2 ≠ R.source := by
            simpa only [sourceIncidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or] using hincident
          simp [childState, active, reachableDecide_all_closed, hne.1, hne.2,
            Ne.symm hne.1, Ne.symm hne.2]
      calc
        _ = ∏ edge, if edge ∈ R.sourceIncidentEdges then charFun (law .single) (t / radius) else 1 := by
          apply Finset.prod_congr rfl
          intro edge _
          exact hfactor edge
        _ = _ := by rw [Finset.prod_ite_mem_eq, Finset.prod_const]
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 2
      ring

theorem allClosed_single_support_sum {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (p radius : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p)
    (hsmoothing : law .single = finiteMixtureLaw (R.conditionalCellWeight p false)
      (R.offspringMassLaw law radius .single))
    (point : Fin R.sourceIncidentEdges.card → ℝ) (hpoint : ∀ edge, point edge ∈ (law .single).support) :
    (∑ edge, point edge) / radius ∈ (law .single).support := by
  have hsum := independent_sum_support (fun _ : Fin R.sourceIncidentEdges.card => law .single) point hpoint
  have hscaled := continuous_map_support _ (fun x : ℝ => radius⁻¹ * x) (by fun_prop) _ hsum
  have hbranch : (∑ edge, point edge) / radius ∈
      (R.offspringMassLaw law radius .single (fun _ => false)).support := by
    rw [R.offspringMassLaw_allClosed_single]
    simpa only [div_eq_mul_inv, mul_comm] using hscaled
  rw [hsmoothing]
  exact finite_mixture_support _ _ (fun _ => false)
    (R.conditionalCellWeight_allClosed_pos p hp hp' hfixed) _ hbranch

theorem childState_allOpen_connected {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex) (edge : Fin edges) :
    R.childState .connected (fun _ => true) edge = some .connected := by
  have hactive (vertex : Fin vertices) : R.active .connected (fun _ => true) vertex = true := by
    simp only [active, show (LiveState.connected == LiveState.both) = false from rfl,
      Bool.false_and, Bool.or_false, SimpleGraph.reachableDecide_eq_true]
    exact hconnected vertex
  simp [childState, hactive]

theorem allOpen_connected_support_scale {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (p radius : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex) (hfixed : R.reliability p = p)
    (hsmoothing : law .connected = finiteMixtureLaw (R.conditionalCellWeight p true)
      (R.offspringMassLaw law radius .connected))
    (point : ℝ) (hpoint : point ∈ (law .connected).support) :
    (edges : ℝ) * point / radius ∈ (law .connected).support := by
  have hpositive : 0 < R.conditionalCellWeight p true (fun _ => true) := by
    have hcross : R.crosses (fun _ => true) = true := (R.crosses_eq_true _).mpr (hconnected _)
    simp only [conditionalCellWeight, hcross, if_pos rfl, ↓reduceIte, hfixed]
    exact div_pos (bernoulliWeight_pos hp hp' _) hp
  have hsum := R.smoothing_branch_support law p radius .connected hsmoothing
    (fun _ => true) hpositive (fun _ => point) (fun edge => by
      simpa only [childMassLaw, R.childState_allOpen_connected hconnected edge] using hpoint)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

end
end Universality.FiniteNetwork
