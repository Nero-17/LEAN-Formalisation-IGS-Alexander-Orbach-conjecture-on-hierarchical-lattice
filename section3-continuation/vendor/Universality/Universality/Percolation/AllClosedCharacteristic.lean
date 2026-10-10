import Universality.Percolation.GenerationMassCharacteristic
import Universality.Percolation.MassRowLowerBounds
import Universality.Probability.CharacteristicRigidity

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

/-- In the all-closed single-terminal configuration the live children are
exactly the source-incident edges, all of single-terminal type. -/
theorem allClosed_characteristic_product (R : FiniteNetwork vertices edges)
    (values : LiveState → ℂ) :
    (∏ e, match R.childState .single (fun _ => false) e with
      | none => 1
      | some child => values child) = values .single ^ R.sourceIncidentEdges.card := by
  classical
  have hfactor (e : Fin edges) :
      (match R.childState .single (fun _ => false) e with
        | none => (1 : ℂ)
        | some child => values child) = if e ∈ R.sourceIncidentEdges then values .single else 1 := by
    by_cases he : e ∈ R.sourceIncidentEdges
    · rw [if_pos he, R.childState_allClosed_single e (Finset.mem_filter.mp he).2]
    · rw [if_neg he]
      have hne : (R.endpoint e).1 ≠ R.source ∧ (R.endpoint e).2 ≠ R.source := by
        simpa only [sourceIncidentEdges, Finset.mem_filter, Finset.mem_univ, true_and, not_or] using he
      simp [childState, active, reachableDecide_all_closed, hne.1, hne.2,
        Ne.symm hne.1, Ne.symm hne.2]
  simp_rw [hfactor]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

theorem conditionalCellWeight_allClosed_pos (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p) :
    0 < R.conditionalCellWeight p false (fun _ => false) := by
  simp only [conditionalCellWeight, R.crosses_all_closed, if_pos rfl, Bool.false_eq_true,
    ↓reduceIte, hfixed]
  exact div_pos (bernoulliWeight_pos hp hp' _) (sub_pos.mpr hp')

/-- Unit modulus in the actual single-state smoothing equation propagates
through the positive-probability all-closed branch. -/
theorem allClosed_characteristic_unit_branch (R : FiniteNetwork vertices edges)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p)
    (values : LiveState → ℂ) (unit : ℂ)
    (hvalues : ∀ child, ‖values child‖ ≤ 1) (hunit : ‖unit‖ = 1)
    (hsmoothing : unit = ∑ coarse, (R.conditionalCellWeight p false coarse : ℂ) *
      ∏ e, match R.childState .single coarse e with
        | none => 1
        | some child => values child) :
    values .single ^ R.sourceIncidentEdges.card = unit := by
  have hproduct (coarse : Configuration edges) :
      ‖∏ e, match R.childState .single coarse e with
        | none => (1 : ℂ)
        | some child => values child‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro e _
    cases R.childState .single coarse e with
    | none => simp
    | some child => exact hvalues child
  have hclosed := weighted_characteristic_eq_unit
    (R.conditionalCellWeight p false)
    (fun coarse => ∏ e, match R.childState .single coarse e with
      | none => (1 : ℂ)
      | some child => values child) unit
    (fun _ => R.conditionalCellWeight_nonneg hp.le hp'.le _ _)
    (R.sum_conditionalCellWeight p (by rwa [hfixed]) (by rwa [hfixed]) false)
    hproduct hunit hsmoothing.symm (fun _ => false)
    (R.conditionalCellWeight_allClosed_pos p hp hp' hfixed)
  rwa [R.allClosed_characteristic_product values] at hclosed

end
end Universality.FiniteNetwork
