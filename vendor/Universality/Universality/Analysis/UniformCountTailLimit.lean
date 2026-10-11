import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Universality
noncomputable section
open Filter
open scoped Topology

/-- Uniform inverse-cutoff tails justify exchanging the volume limit with the
sum of cluster densities, including when root mass escapes to infinity. -/
theorem hasSum_of_uniform_count_tails (rows : ℕ → ℕ → ℝ) (density : ℕ → ℝ)
    (totals : ℕ → ℝ) (total : ℝ)
    (hnonneg : ∀ n size, 0 ≤ rows n size)
    (hpoint : ∀ size, Tendsto (fun n => rows n size) atTop (𝓝 (density size)))
    (htotal : Tendsto totals atTop (𝓝 total))
    (htails : ∀ n cutoff, 0 < cutoff →
      (∑ size ∈ Finset.range cutoff, rows n size) ≤ totals n ∧
      totals n ≤ (∑ size ∈ Finset.range cutoff, rows n size) + 1 / cutoff) :
    HasSum density total := by
  have hpositive (size : ℕ) : 0 ≤ density size :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hpoint size)
      (Eventually.of_forall fun n => hnonneg n size)
  have hbounds (cutoff : ℕ) (hcutoff : 0 < cutoff) :
      0 ≤ total - (∑ size ∈ Finset.range cutoff, density size) ∧
      total - (∑ size ∈ Finset.range cutoff, density size) ≤ 1 / cutoff := by
    have hsum := tendsto_finsetSum (Finset.range cutoff) (fun size _ => hpoint size)
    have hlo := le_of_tendsto_of_tendsto hsum htotal
      (Eventually.of_forall fun n => (htails n cutoff hcutoff).1)
    have hhi := le_of_tendsto_of_tendsto htotal (hsum.add_const (1 / (cutoff : ℝ)))
      (Eventually.of_forall fun n => (htails n cutoff hcutoff).2)
    exact ⟨by linarith, by linarith⟩
  have herror : Tendsto (fun cutoff => total -
      (∑ size ∈ Finset.range cutoff, density size)) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ tendsto_one_div_atTop_nhds_zero_nat
    · filter_upwards [eventually_gt_atTop 0] with cutoff hcutoff
      exact (hbounds cutoff hcutoff).1
    · filter_upwards [eventually_gt_atTop 0] with cutoff hcutoff
      exact (hbounds cutoff hcutoff).2
  apply (hasSum_iff_tendsto_nat_of_nonneg hpositive total).mpr
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => total) atTop (𝓝 total)).sub herror

end
end Universality
