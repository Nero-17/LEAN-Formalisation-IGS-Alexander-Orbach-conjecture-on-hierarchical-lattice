import IGSIII34.Spectral.WeightedSeries
import Mathlib.Order.Filter.Cofinite

/-! The weighted uniform series estimate with genuine eigenbasis indices.
Finite or countably infinite spectra use the same finite-subset filter;
no artificial enumeration or duplicate zero eigenvectors is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

theorem indexed_uniformly_tsum_of_weighted_tail_completion20261011
    {Index Space : Type*} (functions : Index → Space → ℝ)
    (weights : Index → Space → ℝ) (domain : Set Space) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (weightsNonnegative : ∀ index point, 0 ≤ weights index point)
    (weightsSummable : ∀ point ∈ domain, Summable (fun index => weights index point))
    (weightsBound : ∀ point ∈ domain, (∑' index, weights index point) ≤ bound)
    (tailSmall : ∀ tolerance > 0, ∀ᶠ index in cofinite, ∀ point ∈ domain,
      ‖functions index point‖ ≤ tolerance * weights index point) :
    TendstoUniformlyOn
      (fun indices : Finset Index => fun point => ∑ index ∈ indices, functions index point)
      (fun point => ∑' index, functions index point) atTop domain := by
  classical
  have functionSummable : ∀ point ∈ domain, Summable (fun index => functions index point) := by
    intro point membership
    apply (weightsSummable point membership).of_norm_bounded_eventually
    filter_upwards [tailSmall 1 zero_lt_one] with index small
    simpa only [one_mul] using small point membership
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon positive
  have tolerancePositive : 0 < epsilon / (bound + 1) := div_pos positive (by linarith)
  have badFinite := Filter.eventually_cofinite.mp (tailSmall _ tolerancePositive)
  filter_upwards [eventually_ge_atTop badFinite.toFinset] with indices containsBad point membership
  have complementWeights : Summable (fun index : ↑((↑indices : Set Index)ᶜ) => weights index.val point) :=
    (weightsSummable point membership).subtype _
  have complementBound : (∑' index : ↑((↑indices : Set Index)ᶜ), weights index.val point) ≤ bound := by
    have splitting := (weightsSummable point membership).sum_add_tsum_compl (s := indices)
    have finiteNonnegative : 0 ≤ ∑ index ∈ indices, weights index point :=
      Finset.sum_nonneg (fun index _ => weightsNonnegative index point)
    linarith [weightsBound point membership]
  have normBound (index : ↑((↑indices : Set Index)ᶜ)) :
      ‖functions index.val point‖ ≤ epsilon / (bound + 1) * weights index.val point := by
    have notBad : index.val ∉ badFinite.toFinset := fun member => index.property (containsBad member)
    have small : ∀ other ∈ domain,
        ‖functions index.val other‖ ≤ epsilon / (bound + 1) * weights index.val other := by
      by_contra failure
      exact notBad (badFinite.mem_toFinset.mpr failure)
    exact small point membership
  have normSummable : Summable (fun index : ↑((↑indices : Set Index)ᶜ) => ‖functions index.val point‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) normBound (complementWeights.mul_left _)
  have tailBound : ‖∑' index : ↑((↑indices : Set Index)ᶜ), functions index.val point‖ ≤
      epsilon / (bound + 1) * bound := by
    calc
      _ ≤ ∑' index : ↑((↑indices : Set Index)ᶜ), ‖functions index.val point‖ := norm_tsum_le_tsum_norm normSummable
      _ ≤ ∑' index : ↑((↑indices : Set Index)ᶜ), epsilon / (bound + 1) * weights index.val point :=
        normSummable.tsum_le_tsum normBound (complementWeights.mul_left _)
      _ = epsilon / (bound + 1) * (∑' index : ↑((↑indices : Set Index)ᶜ), weights index.val point) := tsum_mul_left
      _ ≤ epsilon / (bound + 1) * bound := mul_le_mul_of_nonneg_left complementBound tolerancePositive.le
  have splitting := (functionSummable point membership).sum_add_tsum_compl (s := indices)
  rw [dist_eq_norm, ← splitting, add_sub_cancel_left]
  apply tailBound.trans_lt
  have multiplied : epsilon / (bound + 1) * (bound + 1) = epsilon := div_mul_cancel₀ _ (by linarith)
  nlinarith

end
end IGSIII34.Spectral

