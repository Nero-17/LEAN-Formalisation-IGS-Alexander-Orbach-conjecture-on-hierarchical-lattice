import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Uniform convergence from a uniformly bounded weighted evaluation sum.
This is the series estimate needed by the spectral construction; it does not
postulate the uniform convergence that it proves. -/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

theorem uniformly_tsum_of_weighted_tail
    {Space : Type*} (functions : ℕ → Space → ℝ)
    (weights : ℕ → Space → ℝ) (domain : Set Space) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (weightsNonnegative : ∀ index point, 0 ≤ weights index point)
    (weightsSummable : ∀ point ∈ domain, Summable (fun index => weights index point))
    (weightsBound : ∀ point ∈ domain, (∑' index, weights index point) ≤ bound)
    (tailSmall : ∀ tolerance > 0, ∀ᶠ index in atTop, ∀ point ∈ domain,
      ‖functions index point‖ ≤ tolerance * weights index point) :
    TendstoUniformlyOn
      (fun depth point => ∑ index ∈ Finset.range depth, functions index point)
      (fun point => ∑' index, functions index point) atTop domain := by
  have functionSummable : ∀ point ∈ domain, Summable (fun index => functions index point) := by
    intro point membership
    apply (weightsSummable point membership).of_norm_bounded_eventually_nat
    filter_upwards [tailSmall 1 zero_lt_one] with index small
    simpa only [one_mul] using small point membership
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon positive
  have tolerancePositive : 0 < epsilon / (bound + 1) := div_pos positive (by linarith)
  obtain ⟨start, afterStart⟩ := eventually_atTop.mp (tailSmall _ tolerancePositive)
  filter_upwards [eventually_ge_atTop start] with depth beyond point membership
  have shiftedWeights : Summable (fun index => weights (index + depth) point) :=
    (weightsSummable point membership).comp_injective (fun _ _ equal => Nat.add_right_cancel equal)
  have shiftedBound : (∑' index, weights (index + depth) point) ≤ bound := by
    have splitting := (weightsSummable point membership).sum_add_tsum_nat_add depth
    have finiteNonnegative : 0 ≤ ∑ index ∈ Finset.range depth, weights index point :=
      Finset.sum_nonneg (fun index _ => weightsNonnegative index point)
    linarith [weightsBound point membership]
  have normBound : ∀ index, ‖functions (index + depth) point‖ ≤
      epsilon / (bound + 1) * weights (index + depth) point := by
    intro index
    exact afterStart _ (beyond.trans (Nat.le_add_left depth index)) point membership
  have normSummable : Summable (fun index => ‖functions (index + depth) point‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) normBound
      (shiftedWeights.mul_left _)
  have tailBound : ‖∑' index, functions (index + depth) point‖ ≤
      epsilon / (bound + 1) * bound := by
    calc
      _ ≤ ∑' index, ‖functions (index + depth) point‖ := norm_tsum_le_tsum_norm normSummable
      _ ≤ ∑' index, epsilon / (bound + 1) * weights (index + depth) point :=
        normSummable.tsum_le_tsum normBound (shiftedWeights.mul_left _)
      _ = epsilon / (bound + 1) * (∑' index, weights (index + depth) point) := tsum_mul_left
      _ ≤ epsilon / (bound + 1) * bound :=
        mul_le_mul_of_nonneg_left shiftedBound tolerancePositive.le
  have splitting := (functionSummable point membership).sum_add_tsum_nat_add depth
  rw [dist_eq_norm, ← splitting, add_sub_cancel_left]
  apply tailBound.trans_lt
  have denominatorPositive : 0 < bound + 1 := by linarith
  have multiplied : epsilon / (bound + 1) * (bound + 1) = epsilon :=
    div_mul_cancel₀ _ denominatorPositive.ne'
  nlinarith

end
end IGSIII34.Spectral
