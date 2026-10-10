import Universality.Percolation.MassSupportBranches

namespace Universality.FiniteNetwork
noncomputable section
open MeasureTheory

theorem childMassLaw_support_nonnegative {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) (hnonnegative : ∀ state, (law state).support ⊆ Set.Ici 0)
    (state : LiveState) (coarse : Configuration edges) (edge : Fin edges) :
    (R.childMassLaw law state coarse edge).support ⊆ Set.Ici 0 := by
  unfold childMassLaw
  cases R.childState state coarse edge with
  | none => exact Measure.support_subset_of_isClosed isClosed_Ici (by simp)
  | some child => exact hnonnegative child

/-- A positive-probability branch containing a selected child embeds its
support affinely into the parent's support; the offset is nonnegative. -/
theorem smoothing_support_affine_transfer {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (hnonnegative : ∀ state, (law state).support ⊆ Set.Ici 0)
    (p radius : ℝ) (hradius : 0 < radius) (state child : LiveState)
    (hsmoothing : law state = finiteMixtureLaw (R.conditionalCellWeight p (state == .connected))
      (R.offspringMassLaw law radius state))
    (coarse : Configuration edges) (hpositive : 0 < R.conditionalCellWeight p (state == .connected) coarse)
    (edge : Fin edges) (hchild : R.childState state coarse edge = some child) :
    ∃ offset : ℝ, 0 ≤ offset ∧ ∀ point ∈ (law child).support,
      point / radius + offset ∈ (law state).support := by
  classical
  choose base hbase using fun e : Fin edges =>
    (R.childMassLaw law state coarse e).nonempty_support (IsProbabilityMeasure.ne_zero _)
  let offset := (∑ e ∈ Finset.univ.erase edge, base e) / radius
  have hbase0 (e : Fin edges) : 0 ≤ base e :=
    R.childMassLaw_support_nonnegative law hnonnegative state coarse e (hbase e)
  refine ⟨offset, div_nonneg (Finset.sum_nonneg (fun e _ => hbase0 e)) hradius.le, ?_⟩
  intro point hpoint
  let value (e : Fin edges) := if e = edge then point else base e
  have hvalue (e : Fin edges) : value e ∈ (R.childMassLaw law state coarse e).support := by
    by_cases he : e = edge
    · subst e
      simpa only [value, if_pos rfl, childMassLaw, hchild] using hpoint
    · simpa only [value, if_neg he] using hbase e
  have hsum : (∑ e, value e) = point + ∑ e ∈ Finset.univ.erase edge, base e := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ edge)]
    have heq : ∑ e ∈ Finset.univ.erase edge, value e = ∑ e ∈ Finset.univ.erase edge, base e := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [value, if_neg (Finset.mem_erase.mp he).1]
    rw [heq]
    simp only [value, if_pos rfl]
    ring
  have hmem := R.smoothing_branch_support law p radius state hsmoothing coarse hpositive value hvalue
  rw [hsum, add_div] at hmem
  exact hmem

end
end Universality.FiniteNetwork
